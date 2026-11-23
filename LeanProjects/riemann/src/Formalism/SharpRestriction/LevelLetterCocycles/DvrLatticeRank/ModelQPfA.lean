import Formalism.SharpRestriction.LevelLetterCocycles.ExpansionFormAll

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def smulE (π' : LetA O n) (c : ZMod n) (e : W.EE) : LA W T π' c →ₗ[O] LA W T π' c :=
  TensorProduct.map (LinearMap.mulLeft O e) LinearMap.id

variable {W T}

theorem smulLA_eq (π' : LetA O n) (c : ZMod n) (a : LetA O n) :
    smulLA W T π' c a = smulE W T π' c (algebraMap (LetA O n) W.EE a) := rfl

theorem smulE_mul (π' : LetA O n) (c : ZMod n) (e f : W.EE) (x : LA W T π' c) :
    smulE W T π' c (e * f) x = smulE W T π' c e (smulE W T π' c f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y l => simp [smulE, mul_assoc]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem smulE_one (π' : LetA O n) (c : ZMod n) (x : LA W T π' c) : smulE W T π' c 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y l => simp [smulE]
  | add x y hx hy => rw [map_add, hx, hy]

theorem smulE_comm (π' : LetA O n) (c : ZMod n) (e f : W.EE) (x : LA W T π' c) :
    smulE W T π' c e (smulE W T π' c f x) = smulE W T π' c f (smulE W T π' c e x) := by
  rw [← smulE_mul, ← smulE_mul, mul_comm]

theorem smulE_unit (π' : LetA O n) (c : ZMod n) (u : W.EEˣ) (x : LA W T π' c) :
    smulE W T π' c (u : W.EE) (smulE W T π' c ((u⁻¹ : W.EEˣ) : W.EE) x) = x := by
  rw [← smulE_mul, Units.mul_inv, smulE_one]

theorem smulE_unit' (π' : LetA O n) (c : ZMod n) (u : W.EEˣ) (x : LA W T π' c) :
    smulE W T π' c ((u⁻¹ : W.EEˣ) : W.EE) (smulE W T π' c (u : W.EE) x) = x := by
  rw [← smulE_mul, Units.inv_mul, smulE_one]

theorem toLA_tmul (π' : LetA O n) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (l : ↥S) :
    toLA W T π' c S (a ⊗ₜ l) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (l : LcQ W T π' c) := by
  simp [toLA]

theorem smulE_tmul (π' : LetA O n) (c : ZMod n) (e f : W.EE) (l : LcQ W T π' c) :
    smulE W T π' c e (f ⊗ₜ l) = (e * f) ⊗ₜ l := by
  simp [smulE]

set_option maxHeartbeats 1000000 in

theorem finite_of (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (hEu : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (h4 : (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c)
    (hLfin : Module.Finite O (LcQ W T π' c))
    (D : ℕ) (S : Fin D → ↥W.AΔ)
    (hdiv : ∀ a : ↥W.AΔ, ∃ (co : Fin D → O) (s : ↥W.AΔ),
      (letE c : LetA O n) * a = (letE c : LetA O n) * (∑ r, algebraMap O (LetA O n) (co r) * (S r : LetA O n)) +
        (letE c : LetA O n) * (π' * Eπ ^ (2 * h') * s)) :
    Module.Finite O (QL W T Pt π' Eπ h' c) := by
  classical
  haveI := hLfin
  obtain ⟨m, gL, hgL⟩ := Module.Finite.exists_fin (R := O) (M := LcQ W T π' c)
  set u : W.EEˣ := hEu.unit with hu
  set Ei : W.EE := ((u⁻¹ ^ h' : W.EEˣ) : W.EE) with hEi
  have hEpow : (algebraMap (LetA O n) W.EE (Eπ ^ h')) = ((u ^ h' : W.EEˣ) : W.EE) := by
    rw [map_pow, Units.val_pow_eq_pow_val, hu, hEu.unit_spec]
  have hEinv : ∀ z, smulLA W T π' c (Eπ ^ h') (smulE W T π' c Ei z) = z := by
    intro z
    rw [smulLA_eq, hEpow, hEi, inv_pow, smulE_unit]
  have hEinv' : ∀ z, smulE W T π' c Ei (smulLA W T π' c (Eπ ^ h') z) = z := by
    intro z
    rw [smulLA_eq, hEpow, hEi, inv_pow, smulE_unit']

  let gens : Fin D × Fin m → LA W T π' c := fun p =>
    toLA W T π' c ⊤ (S p.1 ⊗ₜ (⟨gL p.2, trivial⟩ : ↥(⊤ : Submodule O (LcQ W T π' c))))
  let Sp : Submodule O (LA W T π' c) := Submodule.span O (Set.range gens)
  let Rm : Submodule O (LA W T π' c) :=
    (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (π' * Eπ ^ (2 * h')))
  have key : ∀ τ, toLA W T π' c ⊤ τ ∈ Sp ⊔ Rm := by
    intro τ
    induction τ using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul a l =>
      obtain ⟨co, s, hs⟩ := hdiv a
      rw [toLA_tmul, hs]
      rw [map_add, TensorProduct.add_tmul]
      refine add_mem ?_ ?_
      · refine Submodule.mem_sup_left ?_
        have hl : (l : LcQ W T π' c) ∈ Submodule.span O (Set.range gL) := by rw [hgL]; trivial
        obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hl
        rw [← ho, Finset.mul_sum, map_sum, TensorProduct.tmul_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.sum_tmul]
        refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun r hr => ?_)
        have e1 : algebraMap (LetA O n) W.EE ((letE c : LetA O n) * (algebraMap O (LetA O n) (co r) * (S r : LetA O n))) =
            co r • algebraMap (LetA O n) W.EE ((letE c : LetA O n) * (S r : LetA O n)) := by
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, ← map_mul]
          congr 1
          ring
        rw [e1, ← TensorProduct.smul_tmul']
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(r, j), ?_⟩)
        simp only [gens, toLA_tmul]
      · refine Submodule.mem_sup_right ⟨toLA W T π' c ⊤ (s ⊗ₜ l), LinearMap.mem_range_self _ _, ?_⟩
        rw [toLA_tmul, smulLA_eq, smulE_tmul, ← map_mul]
        congr 2
        ring

  let mkQ := (Submodule.mkQ ((piNL W T Pt π' Eπ h' c 1).comap (LamLA W T π' Eπ h' c ⊤).subtype))
  have hmem : ∀ p, smulE W T π' c Ei (gens p) ∈ LamLA W T π' Eπ h' c ⊤ := by
    intro p
    show smulLA W T π' c (Eπ ^ h') (smulE W T π' c Ei (gens p)) ∈ LinearMap.range (toLA W T π' c ⊤)
    rw [hEinv]
    exact LinearMap.mem_range_self _ _
  refine ⟨⟨Finset.univ.image fun p => mkQ ⟨_, hmem p⟩, ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  have hx0 := hx
  obtain ⟨τ, hτ⟩ := hx
  have hk := key τ
  rw [hτ] at hk
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hk

  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hy
  have hyL1 : smulE W T π' c Ei y ∈ LamLA W T π' Eπ h' c ⊤ := by
    rw [← hcf, map_sum]
    exact Submodule.sum_mem _ fun p _ => by rw [map_smul]; exact Submodule.smul_mem _ _ (hmem p)
  have hyeq : (⟨_, hyL1⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ∑ p, cf p • ⟨_, hmem p⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [← hcf, map_sum]
    exact Finset.sum_congr rfl fun p _ => map_smul _ _ _
  have hyL2 : mkQ ⟨_, hyL1⟩ ∈ Submodule.span O ((Finset.univ.image fun p => mkQ ⟨_, hmem p⟩ : Finset _) :
      Set (QL W T Pt π' Eπ h' c)) := by
    rw [hyeq, map_sum]
    exact Submodule.sum_mem _ fun p _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, Finset.mem_univ _, rfl⟩)))

  have hxe : x = smulE W T π' c Ei y + smulE W T π' c Ei z := by
    rw [← map_add, hyz, hEinv']
  have hsc : Ei * algebraMap (LetA O n) W.EE (π' * Eπ ^ (2 * h')) =
      algebraMap (LetA O n) W.EE (π' ^ 1) * algebraMap (LetA O n) W.EE (Eπ ^ h') := by
    have hvv : (((u ^ h')⁻¹ : W.EEˣ) : W.EE) * ((u ^ h' : W.EEˣ) : W.EE) = 1 := Units.inv_mul _
    rw [pow_one, map_mul, show 2 * h' = h' + h' by ring, pow_add, map_mul, hEpow, hEi, inv_pow]
    linear_combination (algebraMap (LetA O n) W.EE π' * ((u ^ h' : W.EEˣ) : W.EE)) * hvv
  have hzN : smulE W T π' c Ei z ∈ piNL W T Pt π' Eπ h' c 1 := by
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    refine ⟨smulLA W T π' c (Eπ ^ h') z₀, h4 ⟨z₀, hz₀, rfl⟩, ?_⟩
    simp only [smulLA_eq]
    rw [← smulE_mul, ← smulE_mul, hsc]
  have hzL : smulE W T π' c Ei z ∈ LamLA W T π' Eπ h' c ⊤ := by
    have h := sub_mem hx0 hyL1
    rwa [hxe, add_sub_cancel_left] at h
  have hsplit : (⟨x, hx0⟩ : ↥(LamLA W T π' Eπ h' c ⊤)) = ⟨_, hyL1⟩ + ⟨_, hzL⟩ :=
    Subtype.ext (by rw [Submodule.coe_add]; exact hxe)
  have hz0 : mkQ ⟨_, hzL⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hzN
  show mkQ ⟨x, hx0⟩ ∈ _
  rw [hsplit, map_add, hz0, add_zero]
  exact hyL2

theorem tf_of (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (hπu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (h1 : NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤)
    (h5 : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, ∀ k : ℕ, ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c →
      x ∈ NL W T Pt π' Eπ h' c)
    (hsat : ∀ a : O, a ≠ 0 → ∀ z : LA W T π' c, smulLA W T π' c π' z ∈ LinearMap.range (toLA W T π' c ⊤) →
      a • z ∈ LinearMap.range (toLA W T π' c ⊤) → z ∈ LinearMap.range (toLA W T π' c ⊤))
    (hℓ : ∀ a : O, a ≠ 0 → ∃ (k : ℕ) (b : O), ((PD.p : ℕ) : O) ^ k = b * a) :
    ∀ (a : O) (q : QL W T Pt π' Eπ h' c), a ≠ 0 → a • q = 0 → q = 0 := by
  intro a q ha haq
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [← map_smul] at haq
  have hax := (Submodule.Quotient.mk_eq_zero _).1 haq
  obtain ⟨y, hyN, hyx⟩ := hax
  replace hyx : smulLA W T π' c (π' ^ 1) y = a • x := hyx
  set pu : W.EEˣ := hπu.unit with hpu
  have hpuv : algebraMap (LetA O n) W.EE π' = (pu : W.EE) := hπu.unit_spec.symm
  set z : LA W T π' c := smulE W T π' c ((pu⁻¹ : W.EEˣ) : W.EE) x with hzdef
  have hzx : smulLA W T π' c π' z = x := by rw [smulLA_eq, hpuv, hzdef, smulE_unit]
  have hyz : a • z = y := by
    have e1 : y = smulE W T π' c ((pu⁻¹ : W.EEˣ) : W.EE) (smulLA W T π' c (π' ^ 1) y) := by
      rw [pow_one, smulLA_eq, hpuv, smulE_unit']
    rw [e1, hyx, map_smul]
  have hzL : z ∈ LamLA W T π' Eπ h' c ⊤ := by
    show smulLA W T π' c (Eπ ^ h') z ∈ LinearMap.range (toLA W T π' c ⊤)
    refine hsat a ha _ ?_ ?_
    · rw [smulLA_eq, smulLA_eq, smulE_comm, ← smulLA_eq, ← smulLA_eq, hzx]
      exact hx
    · rw [← map_smul, hyz]
      exact h1 hyN
  have hzN : z ∈ NL W T Pt π' Eπ h' c := by
    obtain ⟨k, b, hk⟩ := hℓ a ha
    refine h5 z hzL k ?_
    rw [hk, mul_smul, hyz]
    exact Submodule.smul_mem _ _ hyN
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨z, hzN, ?_⟩
  rw [pow_one, hzx]
  rfl

theorem range_iff {ι : Type} [Fintype ι] [DecidableEq ι] (π' : LetA O n) (c : ZMod n) (bL : Basis ι O (LcQ W T π' c))
    (z : LA W T π' c) :
    z ∈ LinearMap.range (toLA W T π' c ⊤) ↔
      ∀ i, ∃ g ∈ W.AΔ, TensorProduct.equivFinsuppOfBasisRight bL z i =
        algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g) := by
  classical
  constructor
  · rintro ⟨τ, rfl⟩
    induction τ using TensorProduct.induction_on with
    | zero => intro i; exact ⟨0, zero_mem _, by simp⟩
    | add x y hx hy =>
      intro i
      obtain ⟨g, hg, e⟩ := hx i
      obtain ⟨g', hg', e'⟩ := hy i
      refine ⟨g + g', add_mem hg hg', ?_⟩
      rw [map_add, map_add, Finsupp.add_apply, e, e', mul_add, map_add]
    | tmul a l =>
      intro i
      refine ⟨algebraMap O (LetA O n) (bL.repr l i) * a, mul_mem (Subalgebra.algebraMap_mem _ _) a.2, ?_⟩
      rw [toLA_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply,
        Algebra.smul_def, IsScalarTower.algebraMap_apply O (LetA O n) W.EE, ← map_mul]
      congr 1
      ring
  · intro h
    choose g hg e using h
    have hz : z = (TensorProduct.equivFinsuppOfBasisRight bL).symm (TensorProduct.equivFinsuppOfBasisRight bL z) := by simp
    rw [hz, TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
    refine Submodule.sum_mem _ fun i _ => ⟨(⟨g i, hg i⟩ : ↥W.AΔ) ⊗ₜ (⟨bL i, trivial⟩ : ↥(⊤ : Submodule O (LcQ W T π' c))), ?_⟩
    rw [toLA_tmul, e i]

theorem coord_smulE {ι : Type} [Fintype ι] [DecidableEq ι] (π' : LetA O n) (c : ZMod n) (bL : Basis ι O (LcQ W T π' c))
    (e : W.EE) (z : LA W T π' c) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight bL (smulE W T π' c e z) i =
      e * TensorProduct.equivFinsuppOfBasisRight bL z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, mul_add]
  | tmul m l =>
    rw [smulE_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
      Finsupp.mapRange_apply, Finsupp.mapRange_apply, mul_smul_comm]

theorem sat_of {ι : Type} [Fintype ι] [DecidableEq ι] (π' : LetA O n) (c : ZMod n) (bL : Basis ι O (LcQ W T π' c))
    (hlet : ∀ a : O, a ≠ 0 → ∀ u : W.EE,
      (∃ g ∈ W.AΔ, algebraMap (LetA O n) W.EE π' * u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      (∃ g ∈ W.AΔ, a • u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) →
      ∃ g ∈ W.AΔ, u = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * g)) :
    ∀ a : O, a ≠ 0 → ∀ z : LA W T π' c, smulLA W T π' c π' z ∈ LinearMap.range (toLA W T π' c ⊤) →
      a • z ∈ LinearMap.range (toLA W T π' c ⊤) → z ∈ LinearMap.range (toLA W T π' c ⊤) := by
  intro a ha z h1 h2
  rw [range_iff π' c bL] at h1 h2 ⊢
  intro i
  refine hlet a ha _ ?_ ?_
  · obtain ⟨g, hg, e⟩ := h1 i
    exact ⟨g, hg, by rw [← e, smulLA_eq, coord_smulE]⟩
  · obtain ⟨g, hg, e⟩ := h2 i
    exact ⟨g, hg, by rw [← e, map_smul, Finsupp.smul_apply]⟩

end Formalism.MainNotions.N.Ln34.MQ
