import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.ThetaLogCoordinates.ProductIdealMonotone.ProductIdealProofs.ElementarySymmetricExpBound

noncomputable section

open scoped BigOperators Pointwise

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.G0 Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ}

def foldY (G : GAtP p) (m : ℕ) (l : List (Fin G.P.nV)) : G.Fn → G.Fn :=
  l.foldr (fun v f => (G.yv v)^[m] ∘ f) id

theorem foldY_nil (G : GAtP p) (m : ℕ) (x : G.Fn) : foldY G m [] x = x := rfl

theorem foldY_cons (G : GAtP p) (m : ℕ) (v : Fin G.P.nV) (l : List (Fin G.P.nV)) (x : G.Fn) :
    foldY G m (v :: l) x = (G.yv v)^[m] (foldY G m l x) := rfl

private theorem foldY_eq_list_prod_yEnd_pow (G : GAtP p) (m : ℕ) (l : List (Fin G.P.nV)) (x : G.Fn) :
    foldY G m l x = ((l.map fun v => yEnd G v ^ m).prod) x := by
  induction l generalizing x with
  | nil => simp [foldY_nil]
  | cons v l ih =>
    rw [foldY_cons, ih, List.map_cons, List.prod_cons, Module.End.mul_apply, yEnd_pow_apply]

theorem foldY_lin (G : GAtP p) (m : ℕ) (l : List (Fin G.P.nV)) :
    ∃ φ : Module.End G.O G.Fn, ∀ x, foldY G m l x = φ x := by
  exact ⟨(l.map fun v => yEnd G v ^ m).prod, fun x => foldY_eq_list_prod_yEnd_pow G m l x⟩

theorem iter_mem (G : GAtP p) (B : Submodule G.O G.Fn) (hB : ∀ v, ∀ F ∈ B, G.yv v F ∈ B) (v : Fin G.P.nV)
    (m : ℕ) : ∀ x ∈ B, (G.yv v)^[m] x ∈ B := by
  intro x hx
  induction m with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hB v _ ih

theorem foldY_mem (G : GAtP p) (B : Submodule G.O G.Fn) (hB : ∀ v, ∀ F ∈ B, G.yv v F ∈ B) (m : ℕ)
    (l : List (Fin G.P.nV)) : ∀ x ∈ B, foldY G m l x ∈ B := by
  induction l with
  | nil => intro x hx; rw [foldY_nil]; exact hx
  | cons v l ih =>
    intro x hx
    rw [foldY_cons]
    exact iter_mem G B hB v m _ (ih x hx)

theorem monoN_eq (G : GAtP p) (VV B : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ) (x : G.Fn) :
    monoN G VV B m Sv x = ((p : G.O) ^ (∑ v ∈ VV \ B, Sv v)) • foldY G m (B.sort (· ≤ ·)) x := rfl

theorem monoN_smul (G : GAtP p) (VV B : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ) (c : G.O)
    (x : G.Fn) : monoN G VV B m Sv (c • x) = c • monoN G VV B m Sv x := by
  rw [monoN_eq, monoN_eq, foldY_eq_list_prod_yEnd_pow, foldY_eq_list_prod_yEnd_pow, map_smul, smul_smul, smul_smul, mul_comm]

theorem prodIdeal_le (G : GAtP p) (VV : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ)
    (B : Submodule G.O G.Fn) (hB : ∀ v, ∀ F ∈ B, G.yv v F ∈ B) : prodIdeal G VV m Sv B ≤ B := by
  unfold prodIdeal
  rw [Submodule.span_le]
  intro y hy
  simp only [Set.mem_iUnion, Set.mem_image] at hy
  obtain ⟨C, _, x, hx, rfl⟩ := hy
  rw [monoN_eq]
  exact B.smul_mem _ (foldY_mem G B hB m _ x hx)

theorem prodIdeal_shift (G : GAtP p) (VV : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ)
    (A B : Submodule G.O G.Fn) (c : G.O) (h : ∀ x ∈ A, c • x ∈ B) :
    c • prodIdeal G VV m Sv A ≤ prodIdeal G VV m Sv B := by
  have key : prodIdeal G VV m Sv A ≤ (prodIdeal G VV m Sv B).comap (c • LinearMap.id) := by
    unfold prodIdeal
    rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_image] at hy
    obtain ⟨C, hC, x, hx, rfl⟩ := hy
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, ← monoN_smul]
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨C, Set.mem_iUnion.2 ⟨hC, ⟨c • x, h x hx, rfl⟩⟩⟩)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  exact key hz

theorem m_finite (G : GAtP p) (h2 : G.FinClasses) (hs2 : G.M ≤ G.Mna) : Module.Finite G.O G.M := by
  haveI := mna_finite G h2
  exact Module.Finite.of_injective (Submodule.inclusion hs2) (Submodule.inclusion_injective hs2)

private theorem smul_left_cancel_of_ne_zero (G : GAtP p) (v : Fin G.P.nV) (r : G.O) (hr : r ≠ 0) (x y : G.Fn)
    (h : r • x = r • y) : x = y := by
  haveI := (G.P.setting v).frac_O
  have hr0 : algebraMap G.O G.Kf r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective G.O G.Kf)).2 hr
  funext i L
  ext n
  have h' := congrArg (fun F : G.Fn => MvPolynomial.coeff n (F i L)) h
  simp only [Pi.smul_apply, Algebra.smul_def, MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C_mul] at h'
  exact mul_left_cancel₀ hr0 h'

theorem m_free (G : GAtP p) (v : Fin G.P.nV) [Module.Finite G.O G.M] : Module.Free G.O G.M := by
  haveI : Module.IsTorsionFree G.O G.M := by
    constructor
    intro r hr x y hxy
    exact Subtype.ext (smul_left_cancel_of_ne_zero G v r hr.ne_zero x y (congrArg Subtype.val hxy))
  exact Module.free_of_finite_type_torsion_free'

theorem svc_p_ne_zero (G : GAtP p) (v : Fin G.P.nV) : (p : G.O) ≠ 0 := by
  have hS := G.P.setting v
  haveI := hS.frac_alt
  have hW : (p : G.P.W v) ≠ 0 := hS.p_unif.ne_zero
  have hQ : (p : G.P.Qq v) ≠ 0 := by
    rw [← map_natCast (algebraMap (G.P.W v) (G.P.Qq v))]
    exact fun h0 => hW (IsFractionRing.injective (G.P.W v) (G.P.Qq v) (h0.trans (map_zero _).symm))
  have hK : (p : G.Kf) ≠ 0 := by
    rw [← map_natCast (G.P.ι v)]
    exact (map_ne_zero (G.P.ι v)).2 hQ
  intro h
  apply hK
  rw [← map_natCast (algebraMap G.O G.Kf), h, map_zero]

theorem dna_le_d (G : GAtP p) (v : Fin G.P.nV) (e : ℕ) [Module.Finite G.O G.M]
    (hs1 : G.Mna.map (((p : G.O) ^ e) • LinearMap.id) ≤ G.M) : G.dna ≤ G.d := by
  have hp : ((p : G.O) ^ e) ≠ 0 := pow_ne_zero _ (svc_p_ne_zero G v)
  let f : G.Mna →ₗ[G.O] G.M := (((p : G.O) ^ e) • G.Mna.subtype).codRestrict G.M
    (fun x => hs1 (Submodule.mem_map_of_mem x.2))
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((p : G.O) ^ e) • (x : G.Fn) = ((p : G.O) ^ e) • (y : G.Fn) := congrArg Subtype.val hxy
    exact Subtype.ext (smul_left_cancel_of_ne_zero G v _ hp _ _ h1)
  exact LinearMap.finrank_le_finrank_of_injective hf

theorem core (D : Formalism.BasicNotions.D7) (G : GAtP p) (v0 : Fin G.P.nV) (e : ℕ)
    (hs1 : G.Mna.map (((p : G.O) ^ e) • LinearMap.id) ≤ G.M) (hs2 : G.M ≤ G.Mna)
    (h9 : Formalism.MainNotions.SelectionLemmas.Conclusion1 D G) (h12a : ∀ v, ∀ F ∈ G.Mna, G.yv v F ∈ G.Mna)
    (h12b : ∀ v, ∀ F ∈ G.M, G.yv v F ∈ G.M) (h13 : G.FinClasses)
    (VV : Finset (Fin G.P.nV)) (t Sv : Fin G.P.nV → ℕ) (Dd cStar S m : ℕ) (κ : Fin G.P.nV → ℝ)
    (V' : Submodule G.O G.Fn) (hm : 1 ≤ m) (hS : ∀ v ∈ VV, Sv v ≤ S)
    (hLP : ∀ v ∈ VV, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v)
      (G.P.σ v) G.P.w G.P.r (G.P.lam0 v) (t v) Dd (κ v) cStar)
    (hsat : Formalism.MainNotions.SelectionLemmas.IsSaturatedIn (G.M ⊓ V') G.M) (hSig : (m : ℝ) * ∑ v ∈ VV, κ v ≤ 1 / 2) :
    prodIdeal G VV m Sv G.M ⊓ (Ideal.span {(p : G.O) ^ (e + tau VV m Dd t)}) • G.M ⊓ V' ≤
        (Ideal.span {(p : G.O) ^ (e + tau VV m Dd t)}) • (G.M ⊓ V') ∧
    ∃ ℓ : ℕ, Module.length G.O (↥(G.M ⊓ V') ⧸ Submodule.comap (G.M ⊓ V').subtype
        (prodIdeal G VV m Sv G.M ⊓ (Ideal.span {(p : G.O) ^ (e + tau VV m Dd t)}) • G.M ⊓ V')) = ℓ ∧
      (ℓ : ℝ) ≤ ((Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)})).toNat : ℝ) *
        ((G.d : ℝ) * (((e + tau VV m Dd t : ℕ) : ℝ) + 2 * S * ((m : ℝ) * ∑ v ∈ VV, κ v))) := by
  obtain ⟨⟨hthm, -⟩, -⟩ := h9 VV t Sv Dd cStar S m κ hm hS hLP
  have hκ : ∀ v ∈ VV, 0 ≤ κ v := fun v hv => kappa_nonneg' G v (t v) Dd cStar (κ v) (hLP v hv)
  have hs0 : 0 ≤ (m : ℝ) * ∑ v ∈ VV, κ v := mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg hκ)
  have hp0 := svc_p_ne_zero G v0
  have hfin : Module.Finite G.O G.M := m_finite G h13 hs2
  have hfree : Module.Free G.O G.M := m_free G v0
  have hd : G.dna ≤ G.d := dna_le_d G v0 e hs1
  set τ := tau VV m Dd t with hτ
  set N := prodIdeal G VV m Sv G.M with hN
  set Sig : ℝ := (m : ℝ) * ∑ v ∈ VV, κ v with hSigd
  have hshift : ∀ β : ℕ, AllButLE (p : G.O) G.M N
      ⌊(G.dna : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ ((τ + β * S) + e) := fun β =>
    Formalism.InvariantFactorPaths.G0.inverse_shift (p : G.O) G.Mna G.M (prodIdeal G VV m Sv G.Mna) N _ _ e hs2
      (prodIdeal_le G VV m Sv G.Mna h12a)
      (prodIdeal_shift G VV m Sv G.Mna G.M _ (fun x hx => hs1 ⟨x, hx, rfl⟩))
      (prodIdeal_le G VV m Sv G.M h12b) (hthm β)
  obtain ⟨ℓ, hℓ, hb⟩ := lengthFromAllBut (p : G.O) hp0 G.M N G.d rfl (e + τ) S VV.card Sig hs0 hSig
    (by
      intro β _
      obtain ⟨C, hCM, hcard, hx⟩ := hshift β
      refine ⟨C, hCM, ?_, fun x hxM => ?_⟩
      · have h0 : (0 : ℝ) ≤ (G.dna : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)) (esymmOn_nonneg VV κ hκ _)
        have hf : (1 : ℝ) ≤ (β + 1).factorial := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
        have hpw2 : 0 ≤ Sig ^ (β + 1) := pow_nonneg hs0 _
        have hpw : 0 ≤ (G.dna : ℝ) * Sig ^ (β + 1) := mul_nonneg (Nat.cast_nonneg _) hpw2
        calc (C.card : ℝ) ≤ (⌊(G.dna : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ : ℝ) := by
              exact_mod_cast hcard
          _ ≤ (G.dna : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) := Nat.floor_le h0
          _ ≤ (G.dna : ℝ) * Sig ^ (β + 1) / ((β + 1).factorial : ℝ) := esymm_clause VV κ hκ m G.dna (β + 1)
          _ ≤ (G.dna : ℝ) * Sig ^ (β + 1) := div_le_self hpw hf
          _ ≤ (G.d : ℝ) * Sig ^ (β + 1) := mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hpw2
      · have he : e + τ + β * S = τ + β * S + e := by ring
        rw [he]
        exact hx x hxM)
    (by
      refine ManyOrbitsP.allBut_mono (allLE G VV m Sv G.M) le_rfl ?_
      calc ∑ v ∈ VV, Sv v ≤ ∑ _v ∈ VV, S := Finset.sum_le_sum hS
        _ = VV.card * S := by simp)
  refine ⟨?_, ?_⟩
  · intro x hx
    refine sat_clause _ N G.M (G.M ⊓ V') hsat ⟨hx.1, ?_, hx.2⟩
    exact Submodule.smul_le_right hx.1.2
  · have hcomap : Submodule.comap (G.M ⊓ V').subtype
        (N ⊓ (Ideal.span {(p : G.O) ^ (e + τ)}) • G.M ⊓ V') =
        Submodule.comap (G.M ⊓ V').subtype (N ⊓ (Ideal.span {(p : G.O) ^ (e + τ)}) • G.M) := by
      ext ⟨x, hx⟩
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, hx.2⟩⟩
    have hinj := inj_clause (N ⊓ (Ideal.span {(p : G.O) ^ (e + τ)}) • G.M) G.M (G.M ⊓ V') inf_le_left
    have hle := Module.length_le_of_injective _ hinj
    rw [hℓ] at hle
    obtain ⟨ℓ', hℓ', hll⟩ := ENat.le_natCast_iff.1 hle
    refine ⟨ℓ', by rw [hcomap]; exact hℓ', ?_⟩
    calc (ℓ' : ℝ) ≤ ℓ := by exact_mod_cast hll
      _ ≤ _ := hb
      _ = _ := by push_cast; ring

theorem lattice_service_of_place (D : Formalism.BasicNotions.D7) (G : GAtP p) (h0 : 0 < G.P.nV) (hA : Adm6 D G) : Conclusion6 D G := by
  obtain ⟨h9, h10, h12, h13, h3⟩ := hA
  obtain ⟨hs1, hs2⟩ := h10
  obtain ⟨h12a, h12b⟩ := h12
  intro VV t Sv Dd cStar S m κ V' hm hS hLP hsat hSig
  exact core D G ⟨0, h0⟩ G.e hs1 hs2 h9 h12a h12b h13 VV t Sv Dd cStar S m κ V' hm hS hLP hsat hSig

theorem stmt6Loc (D : Formalism.BasicNotions.D7) : LocalServiceStatement D := fun _ G h0 hA => lattice_service_of_place D G h0 hA

theorem stmt6 (D : Formalism.BasicNotions.D7) : ShareFromInputs D := fun _ _ _ h0 hA => lattice_service_of_place D _ h0 hA

theorem stmt6F {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ShareFromInputsFamily Fm := fun _ _ => stmt6 _

theorem foldY_prod (G : GAtP p) (m : ℕ) (l : List (Fin G.P.nV)) (x : G.Fn) :
    foldY G m l x = ((l.map fun v => yEnd G v ^ m).prod) x := by
  exact foldY_eq_list_prod_yEnd_pow G m l x

theorem foldY_perm (G : GAtP p) (m : ℕ) {l l' : List (Fin G.P.nV)} (h : l.Perm l') (x : G.Fn) :
    foldY G m l x = foldY G m l' x := by
  induction h generalizing x with
  | nil => rfl
  | cons v _ ih => rw [foldY_cons, foldY_cons, ih]
  | swap a b l =>
    simp only [foldY_cons, ← yEnd_pow_apply]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ((yEnd_commute G b a).pow_pow m m).eq]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem foldY_smul (G : GAtP p) (m : ℕ) (l : List (Fin G.P.nV)) (c : G.O) (x : G.Fn) :
    foldY G m l (c • x) = c • foldY G m l x := by
  rw [foldY_eq_list_prod_yEnd_pow, foldY_eq_list_prod_yEnd_pow, map_smul]

theorem map_smul_id (G : GAtP p) (a : G.O) (M : Submodule G.O G.Fn) :
    M.map (a • LinearMap.id) = Ideal.span {a} • M := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists]

theorem vUnit_eq (G : GAtP p) (hp0 : (p : G.O) ≠ 0) :
    vUnit G = ((Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)})).toNat : ℝ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible G.O
  obtain ⟨e, u, hau⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hlen : Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)}) = e := by
    rw [hau, Ideal.span_singleton_mul_left_unit u.isUnit]
    exact ln_length_pow ϖ hϖ e
  have hv : IsDiscreteValuationRing.addVal G.O (p : G.O) = e :=
    IsDiscreteValuationRing.addVal_def _ u hϖ e hau
  unfold vUnit
  rw [hlen, hv]

theorem coreT (D : Formalism.BasicNotions.D7) (G : GAtP p) {T : Type} [DecidableEq T] [Nonempty T] (vOf : T → Fin G.P.nV)
    (VVp : Finset T) (e m Dd cStar : ℕ) (tN SN : T → ℕ) (kap : T → ℝ) (Vr : Submodule G.O G.Fn)
    (hs1 : G.Mna.map (((p : G.O) ^ e) • LinearMap.id) ≤ G.M) (hs2 : G.M ≤ G.Mna)
    (h9 : Formalism.MainNotions.SelectionLemmas.Conclusion1 D G) (h12a : ∀ v, ∀ F ∈ G.Mna, G.yv v F ∈ G.Mna)
    (h12b : ∀ v, ∀ F ∈ G.M, G.yv v F ∈ G.M) (h13 : G.FinClasses)
    (hm : 1 ≤ m) (hinj : Set.InjOn vOf (VVp : Set T))
    (hLP : ∀ t0 ∈ VVp, LPprime (W := G.P.W (vOf t0)) (Qq := G.P.Qq (vOf t0)) (O := G.O) (Kf := G.Kf) p
      (G.P.n' (vOf t0)) (G.P.ι (vOf t0)) (G.P.σ (vOf t0)) G.P.w G.P.r (G.P.lam0 (vOf t0)) (tN t0) Dd (kap t0) cStar)
    (hsat : Formalism.MainNotions.SelectionLemmas.IsSaturatedIn (G.M ⊓ Vr) G.M) (hSig : (m : ℝ) * ∑ t0 ∈ VVp, kap t0 ≤ 1 / 2)
    (τ : ℕ) (hτ : τ = e + ∑ t0 ∈ VVp, m * (tN t0 + Dd + 1))
    (NPf : Submodule G.O G.Fn)
    (hNPf : NPf = Submodule.span G.O {F' | ∃ VV' ⊆ VVp, ∃ F ∈ G.M,
      F' = foldY G m (VV'.toList.map vOf) (((p : G.O) ^ (∑ t0 ∈ VVp \ VV', SN t0)) • F)}) :
    NPf ⊓ G.M.map (((p : G.O) ^ τ) • LinearMap.id) ⊓ Vr ≤ (G.M ⊓ Vr).map (((p : G.O) ^ τ) • LinearMap.id) ∧
    ∃ l : ℕ, Module.length G.O (↥(G.M ⊓ Vr) ⧸
        (NPf ⊓ G.M.map (((p : G.O) ^ τ) • LinearMap.id) ⊓ Vr).comap (G.M ⊓ Vr).subtype) = l ∧
      (l : ℝ) ≤ ((Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)})).toNat : ℝ) *
        ((G.d : ℝ) * ((τ : ℝ) + 2 * ((VVp.sup SN : ℕ) : ℝ) * ((m : ℝ) * ∑ t0 ∈ VVp, kap t0))) := by
  classical
  obtain ⟨tt⟩ := ‹Nonempty T›
  have v0 : Fin G.P.nV := vOf tt
  let g : Fin G.P.nV → T := Function.invFunOn vOf (VVp : Set T)
  have hg : ∀ t0 ∈ VVp, g (vOf t0) = t0 := fun t0 h => hinj.leftInvOn_invFunOn h
  have hsumN : ∀ f : T → ℕ, ∑ v ∈ VVp.image vOf, f (g v) = ∑ t0 ∈ VVp, f t0 := by
    intro f
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun t0 h => by rw [hg t0 h])
  have hsumR : ∀ f : T → ℝ, ∑ v ∈ VVp.image vOf, f (g v) = ∑ t0 ∈ VVp, f t0 := by
    intro f
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun t0 h => by rw [hg t0 h])
  have htau : e + tau (VVp.image vOf) m Dd (fun v => tN (g v)) = τ := by
    rw [hτ]
    unfold tau
    rw [hsumN (fun t0 => m * (tN t0 + Dd + 1))]
  obtain ⟨-, ℓ, hℓ, hb⟩ := core D G v0 e hs1 hs2 h9 h12a h12b h13 (VVp.image vOf) (fun v => tN (g v))
    (fun v => SN (g v)) Dd cStar (VVp.sup SN) m (fun v => kap (g v)) Vr hm
    (by
      intro v hv
      obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv
      rw [hg t0 ht0]
      exact Finset.le_sup (f := SN) ht0)
    (by
      intro v hv
      obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv
      rw [hg t0 ht0]
      exact hLP t0 ht0)
    hsat (by rw [hsumR kap]; exact hSig)
  rw [htau, hsumR kap] at hb
  rw [htau] at hℓ
  rw [map_smul_id, map_smul_id]
  refine ⟨?_, ?_⟩
  · intro x hx
    refine sat_clause _ NPf G.M (G.M ⊓ Vr) hsat ⟨hx.1, ?_, hx.2⟩
    exact Submodule.smul_le_right hx.1.2
  · have hle : prodIdeal G (VVp.image vOf) m (fun v => SN (g v)) G.M ≤ NPf := by
      rw [hNPf]
      refine Submodule.span_le.2 ?_
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨B, hB, x, hx, rfl⟩ := hy
      have hB' : B ⊆ VVp.image vOf := Finset.mem_powerset.1 hB
      apply Submodule.subset_span
      refine ⟨VVp.filter (fun t0 => vOf t0 ∈ B), Finset.filter_subset _ _, x, hx, ?_⟩
      rw [monoN_eq, foldY_smul]
      congr 1
      · congr 1
        refine Finset.sum_nbij' g vOf ?_ ?_ ?_ ?_ ?_
        · intro v hv
          obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.1 hv
          obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv1
          rw [hg t0 ht0]
          refine Finset.mem_sdiff.2 ⟨ht0, fun h => hv2 (Finset.mem_filter.1 h).2⟩
        · intro t0 ht0
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ht0
          exact Finset.mem_sdiff.2 ⟨Finset.mem_image_of_mem _ h1, fun h => h2 (Finset.mem_filter.2 ⟨h1, h⟩)⟩
        · intro v hv
          obtain ⟨hv1, -⟩ := Finset.mem_sdiff.1 hv
          obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv1
          rw [hg t0 ht0]
        · intro t0 ht0
          exact hg t0 (Finset.mem_sdiff.1 ht0).1
        · intro v _
          rfl
      · refine foldY_perm G m ?_ x
        refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 ?_
        · refine List.Nodup.map_on ?_ (Finset.nodup_toList _)
          intro a ha b hb hab
          exact hinj (Finset.mem_filter.1 (Finset.mem_toList.1 ha)).1 (Finset.mem_filter.1 (Finset.mem_toList.1 hb)).1 hab
        · intro v
          rw [Finset.mem_sort, List.mem_map]
          constructor
          · intro hv
            obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 (hB' hv)
            exact ⟨t0, Finset.mem_toList.2 (Finset.mem_filter.2 ⟨ht0, hv⟩), rfl⟩
          · rintro ⟨t0, ht0, rfl⟩
            exact (Finset.mem_filter.1 (Finset.mem_toList.1 ht0)).2
    have hle2 : Submodule.comap (G.M ⊓ Vr).subtype
        (prodIdeal G (VVp.image vOf) m (fun v => SN (g v)) G.M ⊓ (Ideal.span {(p : G.O) ^ τ}) • G.M ⊓ Vr) ≤
        Submodule.comap (G.M ⊓ Vr).subtype (NPf ⊓ (Ideal.span {(p : G.O) ^ τ}) • G.M ⊓ Vr) :=
      Submodule.comap_mono (inf_le_inf_right _ (inf_le_inf_right _ hle))
    have hlen := Module.length_le_of_surjective _ (Submodule.factor_surjective hle2)
    rw [hℓ] at hlen
    obtain ⟨ℓ', hℓ', hll⟩ := ENat.le_natCast_iff.1 hlen
    exact ⟨ℓ', hℓ', le_trans (by exact_mod_cast hll) hb⟩

section Record

open Formalism.BasicNotions

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem yProd_eq (Y : LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (VV' : Finset (HH D)) (F : (D.gat u w hg).Fn) :
    yProd Y u w hg VV' F = foldY (D.gat u w hg) D.R.m (VV'.toList.map (Y.vOf u w hg)) F := by
  unfold Formalism.MainNotions.G.yProd
  generalize VV'.toList = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, Function.comp_apply, foldY_cons, ih]

theorem SvG_cast (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (q : ℕ) (t0 : HH D) :
    ((⌈Formalism.MainNotions.G.Sv X K a b q t0⌉.toNat : ℕ) : ℝ) = Formalism.MainNotions.G.Sv X K a b q t0 := by
  have key : ∀ s : ℝ, 0 ≤ s → (((⌈((⌈s⌉ : ℤ) : ℝ)⌉).toNat : ℕ) : ℝ) = ((⌈s⌉ : ℤ) : ℝ) := by
    intro s hs
    rw [Int.ceil_intCast, ← Int.cast_natCast, Int.toNat_of_nonneg (Int.ceil_nonneg hs)]
  unfold Formalism.MainNotions.G.Sv
  exact key _ (Finset.sum_nonneg fun j _ => le_max_left _ _)

theorem stmt6G (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) :
    RamifiedSublatticeVolumeOfAdmissible D L X Y K := by
  intro hA u w hg cStar
  obtain ⟨h9, h12, h13, -⟩ := hA u w hg
  dsimp only
  intro hsand hm hinj hLP hsat hSig
  have v0 : Fin (D.gat u w hg).P.nV := Y.vOf u w hg 0
  have hp0 := svc_p_ne_zero (D.gat u w hg) v0
  by_cases hE : Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅
  · have htau : tauP X K (aL L) (bL L) (D.what₂.places.resChar w) = 0 := by
      unfold tauP
      rw [if_pos hE]
    have hio : ioP X K (aL L) (bL L) (D.what₂.places.resChar w) = 0 := by
      unfold ioP
      rw [dif_neg]
      rw [hE]
      simp
    have hNP : NP X Y K u w hg = (D.gat u w hg).M ⊓ Y.Vram u w hg := by
      apply le_antisymm
      · intro x hx
        refine ⟨?_, hx.2⟩
        have h1 := hx.1.2
        rw [map_smul_id] at h1
        exact Submodule.smul_le_right h1
      · intro x hx
        refine ⟨⟨?_, ?_⟩, hx.2⟩
        · apply Submodule.subset_span
          refine ⟨∅, Finset.empty_subset _, x, hx.1, ?_⟩
          rw [yProd_eq, hE]
          simp [foldY_nil]
        · rw [htau]
          exact ⟨x, hx.1, by simp⟩
    rw [hNP, htau, hio]
    refine ⟨?_, 0, ?_, by simp⟩
    · intro x hx
      exact ⟨x, hx, by simp⟩
    · have htop : Submodule.comap ((D.gat u w hg).M ⊓ Y.Vram u w hg).subtype
          ((D.gat u w hg).M ⊓ Y.Vram u w hg) = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨x, hx⟩ -
        exact hx
      rw [htop]
      simp
  · have hne : (Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w)).Nonempty :=
      Finset.nonempty_iff_ne_empty.2 hE
    have hVV : Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w) =
        goodReps X (D.what₂.places.resChar w) := by
      unfold Formalism.MainNotions.G.VV at hE ⊢
      split_ifs at hE ⊢ with h
      · rfl
      · exact absurd rfl hE
    have hSigEq : Sig X K (aL L) (bL L) (D.what₂.places.resChar w) = (D.R.m : ℝ) *
        ∑ t0 ∈ Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w),
          kapv X K (aL L) (bL L) (D.what₂.places.resChar w) t0 := by
      rw [hVV]
      rfl
    have htauN : tauP X K (aL L) (bL L) (D.what₂.places.resChar w) =
        ((X.ep (D.what₂.places.resChar w) + ∑ t0 ∈ Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w),
          D.R.m * (⌈tv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉₊ + Dp K L (D.what₂.places.resChar w) + 1) : ℕ) : ℝ) := by
      unfold tauP
      rw [if_neg hE]
      push_cast
      rfl
    have hτ : ⌈tauP X K (aL L) (bL L) (D.what₂.places.resChar w)⌉.toNat =
        X.ep (D.what₂.places.resChar w) + ∑ t0 ∈ Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w),
          D.R.m * (⌈tv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉₊ + Dp K L (D.what₂.places.resChar w) + 1) := by
      rw [htauN, Int.ceil_natCast, Int.toNat_natCast]
    have hκ : ∀ t0 ∈ Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w),
        0 ≤ kapv X K (aL L) (bL L) (D.what₂.places.resChar w) t0 := fun t0 ht0 =>
      kappa_nonneg' (D.gat u w hg) _ _ _ cStar _ (hLP t0 ht0)
    obtain ⟨hincl, l, hl, hb⟩ := coreT D (D.gat u w hg) (Y.vOf u w hg)
      (Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w)) (X.ep (D.what₂.places.resChar w)) D.R.m
      (Dp K L (D.what₂.places.resChar w)) cStar
      (fun t0 => ⌈tv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉₊)
      (fun t0 => ⌈Formalism.MainNotions.G.Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat)
      (fun t0 => kapv X K (aL L) (bL L) (D.what₂.places.resChar w) t0) (Y.Vram u w hg)
      hsand.1 hsand.2 h9 h12.1 h12.2 h13 hm hinj hLP hsat hSig _ hτ
      (Submodule.span (D.gat u w hg).O {F' | ∃ VV' ⊆ Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w),
        ∃ F ∈ (D.gat u w hg).M, F' = yProd Y u w hg VV'
          ((((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^
            (∑ t0 ∈ Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w) \ VV',
              ⌈Formalism.MainNotions.G.Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat)) • F)})
      (by simp only [yProd_eq])
    refine ⟨hincl, l, hl, hb.trans ?_⟩
    rw [vUnit_eq _ hp0, hτ, ← htauN]
    have hio : ioP X K (aL L) (bL L) (D.what₂.places.resChar w) =
        2 * Sig X K (aL L) (bL L) (D.what₂.places.resChar w) *
          (Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w)).sup' hne
            (fun t0 => Formalism.MainNotions.G.Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0) := by
      unfold ioP
      rw [dif_pos hne]
    have hsup : (((Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w)).sup
        (fun t0 => ⌈Formalism.MainNotions.G.Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat) : ℕ) : ℝ) ≤
        (Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w)).sup' hne
                  (fun t0 => Formalism.MainNotions.G.Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0) := by
      obtain ⟨t1, ht1, hs⟩ := Finset.exists_mem_eq_sup _ hne
        (fun t0 => ⌈Formalism.MainNotions.G.Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat)
      rw [hs, SvG_cast]
      exact Finset.le_sup' (fun t0 => Formalism.MainNotions.G.Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0) ht1
    rw [hio, hSigEq]
    have hs0 : 0 ≤ (D.R.m : ℝ) * ∑ t0 ∈ Formalism.MainNotions.G.VV X K (aL L) (bL L) (D.what₂.places.resChar w),
          kapv X K (aL L) (bL L) (D.what₂.places.resChar w) t0 :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg hκ)
    have hmul := mul_le_mul_of_nonneg_left hsup hs0
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (b := _) (c := _) ?_
      (Nat.cast_nonneg (α := ℝ) _)) (Nat.cast_nonneg (α := ℝ) _)) (le_of_eq (mul_assoc _ _ _).symm)
    linarith

end Record

end Formalism.MainNotions.FormalGroupSystem.Pf
