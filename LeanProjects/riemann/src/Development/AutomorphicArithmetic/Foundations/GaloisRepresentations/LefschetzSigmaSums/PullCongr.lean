import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open UpperTheory.Gal.LocalSmoothExtension

open CategoryTheory Limits AlgebraicGeometry in
private theorem pull_congr' {B : Scheme.{0}} {R : Type} [Field R] (Θ : UpperTheory.Gal.G3.Th.{0} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (hf : f ≫ p = q) (hf' : f' ≫ p = q) (x : Θ.H p) :
    Θ.pull f hf x = Θ.pull f' hf' x := by
  subst e
  rfl

open CategoryTheory Limits AlgebraicGeometry in

private theorem pull_base {B : Scheme.{0}} {R : Type} [Field R] (Θ : UpperTheory.Gal.G3.Th.{0} B R) {W Z Z' : Scheme.{0}}
    {p : Z ⟶ B} {p' : Z' ⟶ B} (c : W ⟶ Z) {J : Type} [Fintype J] (f : J → (W ⟶ Z')) (A : Θ.H p' →ₗ[R] Θ.H p)
    (r : W ⟶ B) (hc : c ≫ p = r) (hf : ∀ j, f j ≫ p' = r)
    (H : ∀ x, Θ.pull c hc (A x) = ∑ j, Θ.pull (f j) (hf j) x) (hf' : ∀ j, f j ≫ p' = c ≫ p) (x : Θ.H p') :
    Θ.pull c rfl (A x) = ∑ j, Θ.pull (f j) (hf' j) x := by
  subst hc
  exact H x

open CategoryTheory Limits AlgebraicGeometry in

private theorem op_core (hFn : CntFn) (hSum : CntSum) (hSig : SigmaFEt) (hSpl : SigmaSplit)
    (hGal : UpperTheory.Gal.G3.TwGal) (hEx : UpperTheory.Gal.G3.HopEx.{0})
    {B : Scheme.{0}} {Γ : Type} [Group Γ] (X : UpperTheory.Gal.G3.Tower B Γ) (i m : X.ι) (K K' M : Subgroup Γ) (h : Γ)
    (hK : X.K i = K) (hM : X.K m = M) (hMK : M ≤ K) (hKK : K ≤ K')
    (hn : ∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) (hidx : M.relIndex K' ≠ 0)
    (hadm : ∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) (hΔ : ∀ k ∈ K', h * k ∈ X.Δ)
    (a1 : (1 : Γ) ∈ X.Δ) (b1 : ∀ u ∈ X.K m, (1 : Γ) * u * 1⁻¹ ∈ X.K i)
    (aT : ∀ c : K' ⧸ K.subgroupOf K', h * (c.out : Γ) ∈ X.Δ)
    (bT : ∀ c : K' ⧸ K.subgroupOf K', ∀ u ∈ X.K m, h * (c.out : Γ) * u * (h * (c.out : Γ))⁻¹ ∈ X.K i) :
    X.IsFn i (cntFn K K' M h) ∧
    IsFinite (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1) ∧
    Etale (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1) ∧
    ∀ Θ : UpperTheory.Gal.G3.Th.{0} B ℂ, Θ.Good → Θ.IsOp (X.q i) (X.q i)
      (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1)
      (Sigma.desc fun c : K' ⧸ K.subgroupOf K' => X.tr m i (h * (c.out : Γ)) (aT c) (bT c))
      (X.hecke Θ i (cntFn K K' M h)) := by
  subst hK hM
  have hcnt := hFn Γ (X.K i) K' (X.K m) h hKK hn hidx hadm
  have hIsFn : X.IsFn i (cntFn (X.K i) K' (X.K m) h) := by
    refine ⟨fun k hk g => hcnt.1 k hk g, fun g hg => ?_, hcnt.2.2⟩
    obtain ⟨k, hk, c, hc, e⟩ := hcnt.2.1 g hg
    rw [e]
    exact X.Δ.mul_mem (X.K_le i k hk) (hΔ c hc)
  have hne : (X.K i).relIndex K' ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_of_le_left K' hMK
    rw [h0] at hd
    exact hidx (Nat.eq_zero_of_zero_dvd hd)
  haveI : ((X.K i).subgroupOf K').FiniteIndex := ⟨hne⟩
  haveI : IsFinite (X.tr m i 1 a1 b1) := X.fin m i a1 b1
  haveI : Etale (X.tr m i 1 a1 b1) := X.etale m i a1 b1
  have hsig := hSig (X.Z m) (X.Z i) (X.tr m i 1 a1 b1) (K' ⧸ (X.K i).subgroupOf K')
  refine ⟨hIsFn, hsig.1, hsig.2, fun Θ hΘ => ?_⟩
  obtain ⟨Γ₀, _, _, r, cadm, hr, huq, hgal⟩ :=
    hGal X m i ⟨a1, b1⟩ (fun k hk u hu => hn k (hKK hk) u hu)
  letI : Fintype Γ₀ := Fintype.ofFinite Γ₀
  letI : Fintype (K' ⧸ (X.K i).subgroupOf K') := Fintype.ofFinite _
  have HarishChandraLabels : ∀ c ∈ K', X.admitted m i (h * c) := fun c hc => ⟨hΔ c hc, fun u hu => hadm c hc u hu⟩
  have adm : ∀ z : (K' ⧸ (X.K i).subgroupOf K') × Γ₀, X.admitted m i (h * (z.1.out : Γ) * r z.2) :=
    fun z => UpperTheory.Gal.G3.Tower.admitted.mul (cadm z.2) (HarishChandraLabels _ z.1.out.2)
  have ecomp : ∀ z : (K' ⧸ (X.K i).subgroupOf K') × Γ₀,
      (X.tr m m (r z.2) (cadm z.2).1 (cadm z.2).2 ≫
          Sigma.ι (fun _ : K' ⧸ (X.K i).subgroupOf K' => X.Z m) z.1) ≫
        Sigma.desc (fun c : K' ⧸ (X.K i).subgroupOf K' => X.tr m i (h * (c.out : Γ)) (aT c) (bT c)) =
      X.tr m i (h * (z.1.out : Γ) * r z.2) (adm z).1 (adm z).2 := by
    intro z
    rw [Category.assoc, Sigma.ι_desc]
    exact X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  have hspl := hSpl (X.Z m) (X.Z i) (X.Z m) (X.tr m i 1 a1 b1) (K' ⧸ (X.K i).subgroupOf K')
    (X.tr m i 1 a1 b1) Γ₀ (fun x => X.tr m m (r x) (cadm x).1 (cadm x).2) hgal.2.2.2.2.2
  refine ⟨X.Z m, X.tr m i 1 a1 b1, Γ₀, inferInstance, inferInstance,
    fun x => X.tr m m (r x) (cadm x).1 (cadm x).2, (K' ⧸ (X.K i).subgroupOf K') × Γ₀, inferInstance,
    fun z => X.tr m m (r z.2) (cadm z.2).1 (cadm z.2).2 ≫
      Sigma.ι (fun _ : K' ⧸ (X.K i).subgroupOf K' => X.Z m) z.1,
    fun z => by rw [ecomp z, X.tr_q, X.tr_q], hgal, hspl, fun y => ?_⟩
  refine pull_base Θ _ _ _ (X.q m) (X.tr_q m i 1 a1 b1) (fun z => by rw [ecomp z, X.tr_q])
    (fun y => ?_) _ y
  have hHop := (hEx X Θ hΘ i (cntFn (X.K i) K' (X.K m) h) hIsFn).1
  have hop := hHop m hMK (fun g hg => by
    obtain ⟨k, hk, c, hc, e⟩ := hcnt.2.1 g hg
    rw [e]
    exact UpperTheory.Gal.G3.Tower.admitted.mul (HarishChandraLabels c hc) (X.tower_admissible_self hk)) y
  have hsum := hSum Γ (X.K i) K' (X.K m) h hMK hKK hn hadm Γ₀ r hr huq (Θ.H (X.q m))
    (fun g => X.pl Θ m i g y) (fun k hk c hc => X.pl_left Θ (HarishChandraLabels c hc) hk y)
  refine ((by rw [X.pl_eq Θ (show X.admitted m i 1 from ⟨a1, b1⟩)] :
      Θ.pull (X.tr m i 1 a1 b1) (X.tr_q m i 1 a1 b1) (X.hecke Θ i (cntFn (X.K i) K' (X.K m) h) y) =
        X.pl Θ m i 1 (X.hecke Θ i (cntFn (X.K i) K' (X.K m) h) y))).trans
      (hop.trans (hsum.symm.trans (Finset.sum_congr rfl fun z _ => ?_)))
  beta_reduce
  rw [X.pl_eq Θ (adm z)]
  exact pull_congr' Θ (ecomp z).symm _ _ y

theorem UpperTheory.Gal.LocalSmoothExtension.memOp2_of :
    KNNormal → CntFn → CntSum → SigmaFEt → SigmaSplit → UpperTheory.Gal.G3.TwGal → UpperTheory.Gal.G3.HopEx.{0} → MemOp := by
  intro hKN hFn hSum hSig hSpl hGal hEx p _ D G L R _ _ gb k T N J g j
  have hMN : L.KN ↑(g j).M ≤ L.KN ↑N := UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd
  have hMK' : L.KN ↑(g j).M ≤ (g j).K := hMN.trans (g j).le
  have hnorm := hKN p D G L ↑(g j).M
  have hpos : 0 < (↑(g j).M : ℕ) := by
    have := (g j).M.2.1
    omega
  have hidx : (L.KN ↑(g j).M).relIndex (g j).K ≠ 0 := by
    intro h0
    apply hnorm.2 hpos
    rw [← Subgroup.relIndex_mul_relIndex (hHK := hMK') (hKL := (g j).le_one), h0, zero_mul]
  have hΔ : ∀ c ∈ (g j).K, (g j).h * c ∈ T.X.Δ := fun c hc =>
    (T.Δ_eq _).2 (UpperTheory.Gal.Int.Geo.Integ.mul (g j).int
      (UpperTheory.Gal.Int.Geo.integ_of_mem ((g j).le_one hc)))
  have a1 : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have b1 : ∀ u ∈ T.X.K (T.lev (g j).M), (1 : G.GAf) * u * 1⁻¹ ∈ T.X.K (T.lev N) := by
    intro u hu
    rw [T.K_eq] at hu ⊢
    simpa using hMN hu
  have aT : ∀ c : (g j).K ⧸ (L.KN ↑N).subgroupOf (g j).K, (g j).h * (c.out : G.GAf) ∈ T.X.Δ :=
    fun c => hΔ _ c.out.2
  have bT : ∀ c : (g j).K ⧸ (L.KN ↑N).subgroupOf (g j).K, ∀ u ∈ T.X.K (T.lev (g j).M),
      (g j).h * (c.out : G.GAf) * u * ((g j).h * (c.out : G.GAf))⁻¹ ∈ T.X.K (T.lev N) := by
    intro c u hu
    rw [T.K_eq] at hu ⊢
    exact (g j).adm _ c.out.2 u hu
  exact op_core hFn hSum hSig hSpl hGal hEx T.X (T.lev N) (T.lev (g j).M) (L.KN ↑N) (g j).K
    (L.KN ↑(g j).M) (g j).h (T.K_eq N) (T.K_eq _) hMN (g j).le
    (fun c hc u hu => hnorm.1 c ((g j).le_one hc) u hu) hidx (g j).adm hΔ a1 b1 aT bT
