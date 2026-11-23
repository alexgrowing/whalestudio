import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma UpperTheory.Gal.productCup_of_system.yb_val_mul (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v w : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e w b) : Val B e (v * w) (a * b) := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨(loc B e).mul_mem h1 h2, by rw [← map_mul]; rfl⟩

private lemma UpperTheory.Gal.productCup_of_system.yb_val_add (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v w : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e w b) : Val B e (v + w) (a + b) := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨(loc B e).add_mem h1 h2, by rw [← map_add]; rfl⟩

private lemma UpperTheory.Gal.productCup_of_system.yb_val_sub (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v w : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e w b) : Val B e (v - w) (a - b) := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨(loc B e).sub_mem h1 h2, by rw [← map_sub]; rfl⟩

private lemma UpperTheory.Gal.productCup_of_system.yb_val_mem (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {b : L} (hb : b ∈ B) : Val B e b (e ⟨b, hb⟩) :=
  (hV L B e).2.2.1 ⟨b, hb⟩

private lemma UpperTheory.Gal.productCup_of_system.yb_omB_mono {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L}
    (h : B ≤ B') (q : ℕ) : omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma UpperTheory.Gal.productCup_of_system.yb_omB_smul {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L}
    {q : ℕ} {b : L} (hb : b ∈ B) {w : DR ℂ L} (hw : w ∈ omB ℂ L B q) : b • w ∈ omB ℂ L B q := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b', hb', v, hv, rfl⟩ := hy
    refine Submodule.subset_span ⟨b * b', B.mul_mem hb hb', v, hv, ?_⟩
    rw [smul_smul]
  | zero => simp
  | add u v _ _ hu hv =>
    rw [smul_add]
    exact Submodule.add_mem _ hu hv
  | smul a u _ hu =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hu

private lemma UpperTheory.Gal.productCup_of_system.yb_mem_sm {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) {M : Submodule ℂ E} {T : Set S} {r : S} (hr : r ∈ T) {m : E}
    (hm : m ∈ M) : act r m ∈ sm act M T :=
  (le_iSup₂_of_le (f := fun r (_ : r ∈ T) => M.map (act r)) r hr le_rfl) (Submodule.mem_map_of_mem hm)

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private lemma UpperTheory.Gal.productCup_of_system.yb_val_tensor (hV : ValBasic) (e : rB ℂ K' (xv x) {0} →ₐ[ℂ] ℂ)
    (w : rB ℂ K (xv x) {0} →ₐ[ℂ] ℂ)
    (hw : ∀ v c, Val (rB ℂ K (xv x) {0}) w v c →
      Val (rB ℂ K' (xv x) {0}) e (algebraMap K K' v) c ∧ Val (rB ℂ K' (xv x) {0}) e (j2 v) c)
    (t : rB ℂ K (xv x) {0} ⊗[ℂ] rB ℂ K (xv x) {0}) :
    Val (rB ℂ K' (xv x) {0}) e
      (gS j2 (Algebra.TensorProduct.map (rB ℂ K (xv x) {0}).val (rB ℂ K (xv x) {0}).val t))
      (w (Algebra.TensorProduct.lmul' ℂ t)) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    have := UpperTheory.Gal.productCup_of_system.yb_val_mem hV _ e (zero_mem (rB ℂ K' (xv x) {0}))
    have h0 : e ⟨0, zero_mem (rB ℂ K' (xv x) {0})⟩ = 0 := map_zero e
    rw [h0] at this
    simpa using this
  | tmul a b =>
    have ha := (hw _ _ (UpperTheory.Gal.productCup_of_system.yb_val_mem hV _ w a.2)).1
    have hb := (hw _ _ (UpperTheory.Gal.productCup_of_system.yb_val_mem hV _ w b.2)).2
    have := UpperTheory.Gal.productCup_of_system.yb_val_mul hV _ e ha hb
    simpa [gS, Algebra.TensorProduct.lmul'_apply_tmul] using this
  | add a b ha hb =>
    simpa [map_add] using UpperTheory.Gal.productCup_of_system.yb_val_add hV _ e ha hb

private lemma UpperTheory.Gal.productCup_of_system.yb_lmul_map (B : Subalgebra ℂ K) (t : B ⊗[ℂ] B) :
    Algebra.TensorProduct.lmul' ℂ (Algebra.TensorProduct.map B.val B.val t) =
      ((Algebra.TensorProduct.lmul' ℂ t : B) : K) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.lmul'_apply_tmul]
  | add a b ha hb => simp [map_add, ha, hb]

private lemma UpperTheory.Gal.productCup_of_system.yb_val_diag (hV : ValBasic) (e : rB ℂ K' (xv x) {0} →ₐ[ℂ] ℂ)
    (w : rB ℂ K (xv x) {0} →ₐ[ℂ] ℂ)
    (hw : ∀ v c, Val (rB ℂ K (xv x) {0}) w v c →
      Val (rB ℂ K' (xv x) {0}) e (algebraMap K K' v) c ∧ Val (rB ℂ K' (xv x) {0}) e (j2 v) c)
    {s : K ⊗[ℂ] K} (hs : s ∈ (sysZ K x 0).R {0} {0}) (h0 : Algebra.TensorProduct.lmul' ℂ s = 0) :
    Val (rB ℂ K' (xv x) {0}) e (gS j2 s) 0 := by
  obtain ⟨t, rfl⟩ := hs
  have h1 : Algebra.TensorProduct.lmul' ℂ t = 0 := by
    apply Subtype.ext
    have := UpperTheory.Gal.productCup_of_system.yb_lmul_map (rB ℂ K (xv x) {0}) t
    rw [← this]
    simpa using h0
  have := UpperTheory.Gal.productCup_of_system.yb_val_tensor x j2 hV e w hw t
  rw [h1, map_zero] at this
  exact this

end

theorem UpperTheory.Gal.productCup_of_system.yBig_of :
    YCols → YKE → KoszulCocycleExistsWithPrescribedComponent → CechKoszulSystemCocycleGluing → SysOk → RS → PtT → LocMax → FixZ → GMap → DtBasic → ValBasic → RYBasic → OmLoc → YBig := by
  intro hCols hKE hK2 hL2 hOk hRS hPt hLM hFZ hGM hDt hV hRY hOm F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A y1 κ _ _ n z hz h hh
  have y0 : Y0 x j2 := y1.toY0
  have good := (hRY F K K' d x j2 y0).2.1 d
  obtain ⟨-, admT, admB, hex⟩ := hCols F K K' d x j2 Fx A y1 κ n z hz
  let T := sysY x j2 d
  let N : (Mi d ⊕ₗ κ) ⊕ₗ Fin d → ℕ × ℕ := app (app n11 n) n10
  let Z : (Mi d ⊕ₗ κ) ⊕ₗ Fin d → K' := app (gG x j2 z) (gT x j2)
  let r := T.r N Z 0 0
  let r' := T.r n10 (gT x j2) 0 0
  have hSO := hOk d K' (DR ℂ K') T _ N Z good admB
  have hSOT := hOk d K' (DR ℂ K') T (Fin d) n10 (gT x j2) good admT
  have m0 : (0 : Fin (d + 1)) ∈ ({0} : Finset (Fin (d + 1))) := Finset.mem_singleton_self 0
  have hne : ({0} : Finset (Fin (d + 1))).Nonempty := Finset.singleton_nonempty 0
  obtain ⟨hrmem, hcol⟩ := hSO.2.1 {0} {0} 0 m0 0 m0
  obtain ⟨hrmem', hcol'⟩ := hSOT.2.1 {0} {0} 0 m0 0 m0
  have hstab := good.stab {0} {0} hne hne
  have htt : ∀ k, r' k = tt K' x k := by
    intro k
    simp [r', T, Sys.r, Sys.u, n10, gT, sysY, tt, map_div₀, div_eq_mul_inv]
  have hKEt : KE (kos T.act (T.M {0} {0}) r') d := by
    intro m hm c hc
    have hRSi := fun c' => hRS K' (DR ℂ K') T.act (Fin d) (T.M {0} {0}) (T.u n10 0 0) r' (gT x j2)
      (fun _ => rfl) m c'
    have hcz : KE (T.colCx n10 (gT x j2) {0} {0}) d := (hex {0} {0} hne hne).2.1
    rw [hcol'] at hcz
    have e1 := (hRSi c).2.2.2.2
    have hz' : unsc T.act (T.u n10 0 0)⁻¹ c ∈
        (kosT T.act (T.M {0} {0}) (T.u n10 0 0) (gT x j2)).Z m :=
      (hRSi _).2.1.mpr (by rw [e1]; exact hc)
    have := (hRSi _).2.2.1.mp (hcz m hm hz')
    rwa [e1] at this
  have hdt : dtS K' x Finset.univ ∈ omB ℂ K' (rB ℂ K' (xv x) {0}) d := by
    obtain ⟨τ, hτ⟩ := y0.covY.exists_isTop
    simpa using (hDt F K' d x y0.covY τ hτ).2.1 Finset.univ
  have hle0 : rB ℂ K' (xv x) {0} ≤ RY (xv x) j2 {0} {0} := le_sup_left
  let h' : rB ℂ K' (xv x) {0} := (-1) ^ d * h
  let m : DR ℂ K' := (h' : K') • dtS K' x Finset.univ
  have hmM : m ∈ T.M {0} {0} :=
    UpperTheory.Gal.productCup_of_system.yb_omB_smul (hle0 h'.2) (UpperTheory.Gal.productCup_of_system.yb_omB_mono hle0 d hdt)
  have hG : ∀ e0 ∈ Fx, ∀ l, Val (rB ℂ K' (xv x) {0}) e0.1 (r l) 0 := by
    intro e0 hF l
    obtain ⟨w, hw⟩ := hFZ F K K' d x j2 Fx A y1 e0 hF
    have hX0 : algebraMap F K' (x 0 : F) ≠ 0 := (map_ne_zero _).2 (x 0).ne_zero
    have hY0 : j2 (algebraMap F K (x 0 : F)) ≠ 0 :=
      (map_ne_zero _).2 ((map_ne_zero _).2 (x 0).ne_zero)
    rcases l with (l | l) | l
    · let p : Fin (d + 1) → K := fun i => algebraMap F K ((x i : F) / x 0)
      have hp : ∀ i, p i ∈ rB ℂ K (xv x) {0} := fun i =>
        (integralClosure (rA ℂ (xv x) {0}) K).algebraMap_mem
          ⟨(x i : F) / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, i, rfl⟩⟩
      have hva := hw _ _ (UpperTheory.Gal.productCup_of_system.yb_val_mem hV _ w.1 (hp (ofLex l).1))
      have hvb := hw _ _ (UpperTheory.Gal.productCup_of_system.yb_val_mem hV _ w.1 (hp (ofLex l).2))
      have h3 := UpperTheory.Gal.productCup_of_system.yb_val_sub hV _ e0.1 (UpperTheory.Gal.productCup_of_system.yb_val_mul hV _ e0.1 hva.1 hvb.2)
        (UpperTheory.Gal.productCup_of_system.yb_val_mul hV _ e0.1 hvb.1 hva.2)
      rw [mul_comm (w.1 ⟨p (ofLex l).1, _⟩), sub_self] at h3
      convert h3 using 1
      have hA : ∀ i, algebraMap K K' (p i) =
          algebraMap F K' (x i : F) / algebraMap F K' (x 0 : F) := fun i => by
        simp only [p, ← IsScalarTower.algebraMap_apply F K K', map_div₀]
      have hB : ∀ i, j2 (p i) =
          j2 (algebraMap F K (x i : F)) / j2 (algebraMap F K (x 0 : F)) := fun i => by
        simp only [p, map_div₀]
      rw [hA, hA, hB, hB]
      change (sysY x j2 d).mu l * (((((sysY x j2 d).X 0 ^ 1 * (sysY x j2 d).Y 0 ^ 1 : K'ˣ))⁻¹ : K'ˣ) : K') = _
      simp [Sys.mu, sysY]
      field_simp
    · have hs := hz.adm 0 0 l
      have h0 : Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).r n z 0 0 l) = 0 := by
        simp only [Sys.r, map_mul]
        rw [hz.diag l, zero_mul]
      have h3 := UpperTheory.Gal.productCup_of_system.yb_val_diag x j2 hV e0.1 w.1 hw hs h0
      convert h3 using 1
      let g : K ⊗[ℂ] K →* K' := MonoidHomClass.toMonoidHom (gS j2)
      have hX : ∀ i, Units.map g ((sysZ K x 0).X i) = T.X i := fun i => Units.ext (by
        change gS j2 ((algebraMap F K (x i : F)) ⊗ₜ 1) = algebraMap F K' (x i : F)
        simp [gS, ← IsScalarTower.algebraMap_apply])
      have hY : ∀ i, Units.map g ((sysZ K x 0).Y i) = T.Y i := fun i => Units.ext (by
        change gS j2 ((1 : K) ⊗ₜ (algebraMap F K (x i : F))) = j2 (algebraMap F K (x i : F))
        simp [gS])
      have hu : Units.map g ((sysZ K x 0).u n 0 0 l) = T.u n 0 0 l := by
        simp [Sys.u, map_mul, map_pow, hX, hY]
      change gS j2 (z l) * (((T.u n 0 0 l)⁻¹ : K'ˣ) : K') =
        gS j2 (z l * ((((sysZ K x 0).u n 0 0 l)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K))
      rw [map_mul, ← hu, ← map_inv]
      rfl
    · change Val _ e0.1 (r' l) 0
      rw [htt]
      have := UpperTheory.Gal.productCup_of_system.yb_val_mem hV _ e0.1 (tco_mem ℂ K' (xv x) l)
      rw [e0.2 l] at this
      exact this
  have hkey : ∀ l, T.act (r l) m ∈ sm T.act (T.M {0} {0}) (Set.range r') := by
    intro l
    have hy : T.act (r l) m ∈ T.M {0} {0} := hstab _ (hrmem l) _ hmM
    refine (hKE F K K' d x j2 y0 (Fin d) r' {0} {0} hne hrmem').2.2 _ hy fun e he => ?_
    obtain ⟨e0, -, hloc, hval⟩ := hPt F K K' d x j2 y0 {0} {0} 0 m0 0 m0 e he
    have hv0 : Val (rB ℂ K' (xv x) {0}) e0.1 (r l * (h' : K')) 0 := by
      by_cases hF : e0 ∈ Fx
      · have := UpperTheory.Gal.productCup_of_system.yb_val_mul hV _ e0.1 (hG e0 hF l)
          (UpperTheory.Gal.productCup_of_system.yb_val_mem hV _ e0.1 h'.2)
        simpa using this
      · have hr := (hval _ _).1 (UpperTheory.Gal.productCup_of_system.yb_val_mem hV _ e (hrmem l))
        have hh0 := (hV K' _ e0.1).2.2.1 h'
        have h00 : e0.1 h' = 0 := by
          simp [h', hh e0 hF]
        rw [h00] at hh0
        simpa using UpperTheory.Gal.productCup_of_system.yb_val_mul hV _ e0.1 hr hh0
    obtain ⟨a, ha, hva⟩ := hLM F K' d x y0.covY y0.red e0 _ hv0
    have hy' : T.act (r l) m = ∑ k, T.act (r' k) (a k • dtS K' x Finset.univ) := by
      change r l • (h' : K') • dtS K' x Finset.univ =
        ∑ k, r' k • (a k • dtS K' x Finset.univ)
      rw [smul_smul, hva, Finset.sum_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, htt k, mul_comm]
    rw [hy']
    refine Submodule.sum_mem _ fun k _ => UpperTheory.Gal.productCup_of_system.yb_mem_sm _ (Set.mem_range_self k) ?_
    rw [hloc]
    exact UpperTheory.Gal.productCup_of_system.yb_omB_smul (ha k) (UpperTheory.Gal.productCup_of_system.yb_omB_mono (hV K' _ e0.1).1 d hdt)
  obtain ⟨c1, hc1, hc1v⟩ := hK2 K' (DR ℂ K') T.act _ (T.R {0} {0}) (T.M {0} {0}) r d inrE hstab hrmem
    hKEt m hmM hkey
  let u := T.u N 0 0
  have hRSb := fun c' => hRS K' (DR ℂ K') T.act _ (T.M {0} {0}) u r Z (fun _ => rfl) d c'
  have e1 := (hRSb c1).2.2.2.2
  let c00 := unsc T.act u⁻¹ c1
  have hc00 : c00 ∈ (T.colCx N Z {0} {0}).Z d := by
    rw [hcol]
    exact (hRSb _).2.1.mpr (by rw [e1]; exact hc1)
  let c0 : Fin (d + 1) → Fin (d + 1) → Finset ((Mi d ⊕ₗ κ) ⊕ₗ Fin d) → DR ℂ K' :=
    fun i j => if i = 0 ∧ j = 0 then c00 else 0
  have hc0Z : ∀ i j, c0 i j ∈ (T.colCx N Z {i} {j}).Z d := by
    intro i j
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      simpa [c0] using hc00
    · simp only [c0, if_neg hij]
      exact zero_mem _
  have hmono := hSO.2.2
  have hI : ∀ i i' j, c0 i j - c0 i' j ∈ (T.colCx N Z {i, i'} {j}).B d := by
    intro i i' j
    by_cases hii : i = i'
    · subst hii
      simp
    · have hI2 : ({i, i'} : Finset (Fin (d + 1))) ≠ {0} := by
        intro he
        have h1 : i ∈ ({0} : Finset (Fin (d + 1))) := he ▸ by simp
        have h2 : i' ∈ ({0} : Finset (Fin (d + 1))) := he ▸ by simp
        exact hii ((Finset.mem_singleton.1 h1).trans (Finset.mem_singleton.1 h2).symm)
      have hn : ({i, i'} : Finset (Fin (d + 1))).Nonempty := ⟨i, by simp⟩
      have hB := ((hex {i, i'} {j} hn (Finset.singleton_nonempty j)).2.2.2 (Or.inl hI2) d).2
      refine hB (sub_mem ?_ ?_)
      · exact hmono {i} {i, i'} {j} {j} (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)
          (by simp) subset_rfl d (hc0Z i j)
      · exact hmono {i'} {i, i'} {j} {j} (Finset.singleton_nonempty i') (Finset.singleton_nonempty j)
          (by simp) subset_rfl d (hc0Z i' j)
  have hJ : ∀ i j j', c0 i j - c0 i j' ∈ (T.colCx N Z {i} {j, j'}).B d := by
    intro i j j'
    by_cases hjj : j = j'
    · subst hjj
      simp
    · have hJ2 : ({j, j'} : Finset (Fin (d + 1))) ≠ {0} := by
        intro he
        have h1 : j ∈ ({0} : Finset (Fin (d + 1))) := he ▸ by simp
        have h2 : j' ∈ ({0} : Finset (Fin (d + 1))) := he ▸ by simp
        exact hjj ((Finset.mem_singleton.1 h1).trans (Finset.mem_singleton.1 h2).symm)
      have hn : ({j, j'} : Finset (Fin (d + 1))).Nonempty := ⟨j, by simp⟩
      have hB := ((hex {i} {j, j'} (Finset.singleton_nonempty i) hn).2.2.2 (Or.inr hJ2) d).2
      refine hB (sub_mem ?_ ?_)
      · exact hmono {i} {i} {j} {j, j'} (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)
          subset_rfl (by simp) d (hc0Z i j)
      · exact hmono {i} {i} {j'} {j, j'} (Finset.singleton_nonempty i) (Finset.singleton_nonempty j')
          subset_rfl (by simp) d (hc0Z i j')
  obtain ⟨c, hc, hcol2⟩ := hL2 d K' _ T _ N Z good admB (fun I J hI hJ => (hex I J hI hJ).2.2.1) c0 hc0Z hI hJ
  refine ⟨c, hc, ?_, ?_⟩
  · have h1 : c (uni (uni {0} {0}) (img inrE)) = c0 0 0 (img inrE) := congrFun (hcol2 0 0) (img inrE)
    have hu : ∀ j : Fin d, u (inrE j) = T.X 0 := fun j => by
      change T.X 0 ^ 1 * T.Y 0 ^ 0 = T.X 0
      simp
    have hp : (∏ l ∈ img (inrE : Fin d ↪o (Mi d ⊕ₗ κ) ⊕ₗ Fin d), u⁻¹ l)⁻¹ = T.X 0 ^ d := by
      simp [img, Finset.prod_map, hu]
    have h2 : c0 0 0 (img inrE) = T.act ((T.X 0 ^ d : K'ˣ) : K') m := by
      simp only [c0, c00, unsc, and_self, if_true]
      rw [hp, hc1v]
    rw [h1, h2]
    change (((T.X 0 ^ d : K'ˣ) : K')) • (h' : K') • dtS K' x Finset.univ = _
    rw [smul_smul]
    congr 1
    simp [T, h', sysY]
    ring
  · intro i j hij
    rw [hcol2]
    have : ¬ (i = 0 ∧ j = 0) := by
      rintro ⟨rfl, rfl⟩
      simp at hij
    simp only [c0, if_neg this]
