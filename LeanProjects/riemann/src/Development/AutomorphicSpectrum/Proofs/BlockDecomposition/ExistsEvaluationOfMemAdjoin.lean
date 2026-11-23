import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.RhoSurj
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.Lift

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (GlRel KHighest)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.LK (ev allT)

variable {n : ℕ}

def kap : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Lt n) :=
  FreeAlgebra.lift ℂ fun p => FreeAlgebra.ι ℂ (true, p) + FreeAlgebra.ι ℂ (false, p)

def Cyc2 {V : Type} [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  LinearMap.range ((LinearMap.applyₗ v).comp (ev2 E1 E2).toLinearMap)

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V] {E1 E2 : Fin n → Fin n → Module.End ℂ V}

theorem mem_cyclic_span_iff {v w : V} : w ∈ Cyc2 E1 E2 v ↔ ∃ a, ev2 E1 E2 a v = w := Iff.rfl

theorem evaluation_kappa (r : FreeAlgebra ℂ (Fin n × Fin n)) :
    ev2 E1 E2 (kap r) = ev (fun a b => E1 a b + E2 a b) r := by
  have : (ev2 E1 E2).comp kap = ev (fun a b => E1 a b + E2 a b) := by
    ext p
    simp [kap, ev2, ev]
  exact DFunLike.congr_fun this r

theorem cyclic_span_stable_alt {v w : V} (c d : Fin n) (h : w ∈ Cyc2 E1 E2 v) : (E1 c d + E2 c d) w ∈ Cyc2 E1 E2 v := by
  obtain ⟨a, rfl⟩ := mem_cyclic_span_iff.1 h
  exact mem_cyclic_span_iff.2 ⟨(FreeAlgebra.ι ℂ (true, c, d) + FreeAlgebra.ι ℂ (false, c, d)) * a, by simp [ev2]⟩

theorem exists_evaluation_of_mem_adjoin {x : Module.End ℂ V}
    (hx : x ∈ Algebra.adjoin ℂ {x : Module.End ℂ V | ∃ a b, x = E1 a b ∨ x = E2 a b}) :
    ∃ a, ev2 E1 E2 a = x := by
  have hle : Algebra.adjoin ℂ {x : Module.End ℂ V | ∃ a b, x = E1 a b ∨ x = E2 a b} ≤ (ev2 E1 E2).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a, b, rfl | rfl⟩
    · exact ⟨FreeAlgebra.ι ℂ (true, a, b), by simp [ev2]⟩
    · exact ⟨FreeAlgebra.ι ℂ (false, a, b), by simp [ev2]⟩
  obtain ⟨a, ha⟩ := hle hx
  exact ⟨a, ha⟩

theorem sum_gl (h : Pair2 E1 E2) : GlRel fun a b => E1 a b + E2 a b := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have e : (E1 a b + E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b + E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) +
        (E1 a b * E2 c d - E2 c d * E1 a b) - (E1 c d * E2 a b - E2 a b * E1 c d) := by noncomm_ring
  show (E1 a b + E2 a b) * (E1 c d + E2 c d) - (E1 c d + E2 c d) * (E1 a b + E2 a b) = _
  rw [e, h1, h2, c1, c2]
  beta_reduce
  split_ifs <;> abel

theorem ad_letter (h : Pair2 E1 E2) (c d : Fin n) (s : Bool) (a b : Fin n) :
    (E1 c d + E2 c d) * (if s then E1 a b else E2 a b) - (if s then E1 a b else E2 a b) * (E1 c d + E2 c d) =
      (if d = a then (if s then E1 c b else E2 c b) else 0) - (if b = c then (if s then E1 a d else E2 a d) else 0) := by
  cases s
  · have h2 := h.gl2 c d a b
    have c1 := h.comm c d a b
    simp only [Bool.false_eq_true, if_false]
    rw [add_mul, mul_add, c1]
    have : E2 a b * E1 c d + E2 c d * E2 a b - (E2 a b * E1 c d + E2 a b * E2 c d) =
      E2 c d * E2 a b - E2 a b * E2 c d := by abel
    rw [this, h2]
  · have h1 := h.gl1 c d a b
    have c1 := h.comm a b c d
    simp only [if_true]
    rw [add_mul, mul_add, ← c1]
    have : E1 c d * E1 a b + E1 a b * E2 c d - (E1 a b * E1 c d + E1 a b * E2 c d) =
      E1 c d * E1 a b - E1 a b * E1 c d := by abel
    rw [this, h1]

end Alg

def AdFam {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Lt n)) (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V), Pair2 E1 E2 →
    ∀ c d i, (E1 c d + E2 c d) * ev2 E1 E2 (w i) - ev2 E1 E2 (w i) * (E1 c d + E2 c d) =
      ∑ j, M c d j i • ev2 E1 E2 (w j)

theorem exists_adFam (a : FreeAlgebra ℂ (Lt n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Lt n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFam w M ∧ a = ∑ i, t i • w i := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩
    · intro c d i j; simp
    · intro V _ _ E1 E2 _ c d i; simp
    · simp [Algebra.algebraMap_eq_smul_one]
  | grade1 x =>
    refine ⟨Lt n, inferInstance, fun p => FreeAlgebra.ι ℂ p,
      fun c d => Matrix.of fun j i => (if d = i.2.1 ∧ j = (i.1, c, i.2.2) then 1 else 0) -
        (if i.2.2 = c ∧ j = (i.1, i.2.1, d) then 1 else 0),
      Pi.single x 1, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨s, i1, i2⟩ ⟨s', j1, j2⟩
      simp only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]
      congr 1
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h2.symm, h3.symm, h1⟩
    · rintro V _ _ E1 E2 hE c d ⟨s, a, b⟩
      have h := ad_letter hE c d s a b
      simp only [ev2, FreeAlgebra.lift_ι_apply, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [h]
      congr 1
      · by_cases h1 : d = a
        · simp only [h1, true_and, if_true, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ]
        · simp [h1]
      · by_cases h1 : b = c
        · simp only [h1, true_and, if_true, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ]
        · simp [h1]
    · simp [Pi.single_apply]
  | mul a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2,
      fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0),
      fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]
    · rintro V _ _ E1 E2 hE c d ⟨i, i'⟩
      have e1 := h2 V E1 E2 hE c d i
      have e2 := h2' V E1 E2 hE c d i'
      have : (E1 c d + E2 c d) * ev2 E1 E2 (w i * w' i') - ev2 E1 E2 (w i * w' i') * (E1 c d + E2 c d) =
          ((E1 c d + E2 c d) * ev2 E1 E2 (w i) - ev2 E1 E2 (w i) * (E1 c d + E2 c d)) * ev2 E1 E2 (w' i') +
            ev2 E1 E2 (w i) * ((E1 c d + E2 c d) * ev2 E1 E2 (w' i') - ev2 E1 E2 (w' i') * (E1 c d + E2 c d)) := by
        rw [map_mul]; noncomm_ring
      simp only []
      rw [this, e1, e2]
      simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm]
      congr 1
      rw [Finset.sum_comm]
      simp
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
  | add a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d),
      Sum.elim t t', ⟨?_, ?_⟩, ?_⟩
    · rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]
    · rintro V _ _ E1 E2 hE c d (i | i)
      · simp [Fintype.sum_sum_type, h2 V E1 E2 hE]
      · simp [Fintype.sum_sum_type, h2' V E1 E2 hE]
    · simp [Fintype.sum_sum_type]

theorem AdFam.comm {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Lt n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFam w M) {V : Type} [AddCommGroup V] [Module ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hE : Pair2 E1 E2) (c d : Fin n) (t : ι → ℂ) :
    (E1 c d + E2 c d) * ev2 E1 E2 (∑ i, t i • w i) - ev2 E1 E2 (∑ i, t i • w i) * (E1 c d + E2 c d) =
      ev2 E1 E2 (∑ j, (M c d *ᵥ t) j • w j) := by
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub, h.2 V E1 E2 hE, Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul,
    smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem invLift2 {V : Type} [AddCommGroup V] [Module ℂ V] {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hE : Pair2 E1 E2)
    (L : Submodule ℂ V) (a : FreeAlgebra ℂ (Lt n)) (hL : ∀ c d, ∀ s ∈ L, (E1 c d + E2 c d) s ∈ L)
    (ha : ∀ c d, ∀ s ∈ L, (E1 c d + E2 c d) (ev2 E1 E2 a s) = ev2 E1 E2 a ((E1 c d + E2 c d) s)) :
    ∃ a', Inv2 a' ∧ ∀ s ∈ L, ev2 E1 E2 a' s = ev2 E1 E2 a s := by
  classical
  obtain ⟨ι, _, w, M, t, hM, rfl⟩ := exists_adFam a
  let N : Submodule ℂ (EuclideanSpace ℂ ι) :=
    { carrier := {x | ∀ s ∈ L, ev2 E1 E2 (∑ i, x i • w i) s = 0}
      add_mem' := by
        intro x y hx hy s hs
        have := hx s hs
        have := hy s hs
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, *, add_zero]
      zero_mem' := by intro s hs; simp
      smul_mem' := by
        intro r x hx s hs
        have := hx s hs
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this,
          smul_zero] }
  have hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, ev2 E1 E2 (∑ i, x i • w i) s = 0 := fun x => Iff.rfl
  let D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι) := fun c d => Matrix.toEuclideanLin (M c d)
  have hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp := fun c d x => rfl
  have hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ := by
    intro c d x y
    have : M d c = (M c d)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]
    simp only [D]
    rw [this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hDN : ∀ c d, ∀ x ∈ N, D c d x ∈ N := by
    intro c d x hx
    rw [hN] at hx ⊢
    intro s hs
    rw [hD, ← hM.comm hE]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d s hs), map_zero, sub_zero]
  have ht : ∀ c d, D c d (WithLp.toLp 2 t) ∈ N := by
    intro c d
    rw [hN]
    intro s hs
    rw [hD, ← hM.comm hE]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ha c d s hs, sub_self]
  obtain ⟨k, hk, t', ht', e⟩ := N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)
  have h0 : ∀ c d, D c d t' = 0 := by
    intro c d
    have h1 : D c d t' ∈ N := by
      have := N.sub_mem (ht c d) (hDN c d k hk)
      rwa [e, map_add, add_sub_cancel_left] at this
    rw [← inner_self_eq_zero (𝕜 := ℂ), hadj]
    exact (Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c _ h1)
  refine ⟨∑ i, t' i • w i, ?_, ?_⟩
  · intro V' _ _ E1' E2' hE' c d
    have := hM.comm hE' c d t'.ofLp
    rw [← hD, h0 c d] at this
    have h2 : ev2 E1' E2' (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0 := by simp
    rw [h2] at this
    exact sub_eq_zero.1 this
  · intro s hs
    have e' : ∀ i, t i = k i + t' i := fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e
    have := (hN k).1 hk s hs
    simp only [e', add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, this, zero_add]

theorem liftInv : LiftInv := by
  classical
  intro n V _ _ E1 E2 hP hU hF μ v w hv0 hv hw hx
  obtain ⟨x, hx, hxv⟩ := hx
  have hgl : GlRel (kF E1 E2) := sum_gl hP
  have hK : KRel (allT n) (kF E1 E2) := fun a b c d _ _ => hgl a b c d
  have hKU : KUnit (allT n) (kF E1 E2) := fun a b _ x y => hU a b x y
  have hFS : ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ KStab (allT n) (kF E1 E2) S ∧ x ∈ S := by
    intro x
    obtain ⟨S, hS, hxS, hSt⟩ := hF x
    exact ⟨S, hS, fun a b _ y hy => hSt a b y hy, hxS⟩
  have hv' : KHighest (allT n) (kF E1 E2) μ v := hv
  have hw' : KHighest (allT n) (kF E1 E2) μ w := hw
  obtain ⟨S, hS, hSt, hvS⟩ := hFS v
  obtain ⟨L, hLS, hvL, hLt, hirr, -, -⟩ :=
    CompanionTheory.D.DSIC.hLowSpan n (allT n) V (kF E1 E2) μ v S hK hKU hv0 hv' hS hSt hvS
  haveI : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLS
  obtain ⟨S', hS', hSt', hwS'⟩ := hFS w
  let EL : Fin n → Fin n → Module.End ℂ L := fun a b => (kF E1 E2 a b).restrict (hLt a b rfl)
  have hEL : ∀ a b (y : L), (EL a b y : V) = kF E1 E2 a b y := fun a b y => by simp [EL]
  obtain ⟨φ, hφv, hφ⟩ := CompanionTheory.D.DSIC.hHWMap n (allT n) L V EL (kF E1 E2) μ ⟨v, hvL⟩ w S'
    (fun a b c d _ _ => by
      ext y
      have := congrArg (fun T : Module.End ℂ V => T y) (hgl a b c d)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hEL] at this ⊢
      rw [this]
      congr 1
      · split_ifs with h
        · subst h; exact (hEL _ _ y).symm
        · rfl
      · split_ifs with h
        · subst h; exact (hEL _ _ y).symm
        · rfl)
    (fun a b _ x y => by
      rw [Submodule.coe_inner, Submodule.coe_inner, hEL, hEL]; exact hU a b x y)
    hK hKU (fun h => hv0 (congrArg Subtype.val h))
    ⟨fun a => Subtype.ext (by rw [hEL]; exact hv.1 a),
      fun a b hab h => Subtype.ext (by rw [hEL]; exact hv.2 a b hab h)⟩ hw' hS' hSt' hwS'
  have hφc : ∀ s, φ s ∈ Cyc2 E1 E2 v := by
    let L' : Submodule ℂ V := ((Cyc2 E1 E2 v).comap φ).map L.subtype
    have h1 : L' = L := by
      refine (hirr L' (Submodule.map_subtype_le _ _) ?_).resolve_left fun hb => hv0 ?_
      · rintro a b h _ ⟨y, hy, rfl⟩
        refine ⟨EL a b y, ?_, hEL a b y⟩
        show φ (EL a b y) ∈ Cyc2 E1 E2 v
        rw [hφ a b rfl]
        exact cyclic_span_stable_alt (E1 := E1) (E2 := E2) a b hy
      · have : v ∈ L' := by
          obtain ⟨a, ha⟩ := exists_evaluation_of_mem_adjoin hx
          exact ⟨⟨v, hvL⟩, by
            show φ ⟨v, hvL⟩ ∈ Cyc2 E1 E2 v
            rw [hφv]
            exact mem_cyclic_span_iff.2 ⟨a, by rw [ha, hxv]⟩, rfl⟩
        simpa [hb] using this
    intro s
    obtain ⟨y, hy, e⟩ : (s : V) ∈ L' := by rw [h1]; exact s.2
    rw [← Subtype.ext e]; exact hy
  have hs := GlobalTheory.CompanionTheory.LKDens.rho_surj (allT n) (kF E1 E2) L hLt hv0 hvL hirr
  let b := Module.finBasis ℂ L
  obtain ⟨a0, ha0⟩ : ∃ a, ∀ s : L, ev2 E1 E2 a s = φ s := by
    choose u hu using fun i => mem_cyclic_span_iff.1 (hφc (b i))
    choose r hr using fun i => hs ((b.coord i).smulRight (⟨v, hvL⟩ : L))
    refine ⟨∑ i, u i * kap (GlobalTheory.CompanionTheory.LKDens.psi (allT n) (r i)), fun s => ?_⟩
    have hk : ∀ i, ev2 E1 E2 (kap (GlobalTheory.CompanionTheory.LKDens.psi (allT n) (r i))) s = (b.repr s i) • v := by
      intro i
      have h1 := GlobalTheory.CompanionTheory.LKDens.ev_psi (allT n) (kF E1 E2) L hLt (r i) s
      rw [hr] at h1
      have h2 : ev2 E1 E2 (kap (GlobalTheory.CompanionTheory.LKDens.psi (allT n) (r i))) =
          ev (kF E1 E2) (GlobalTheory.CompanionTheory.LKDens.psi (allT n) (r i)) := evaluation_kappa _
      rw [h2]
      simpa using h1
    conv_rhs => rw [← b.sum_repr s]
    simp only [map_sum, map_mul, LinearMap.sum_apply, Module.End.mul_apply, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk i, map_smul, hu i]
  obtain ⟨a, hinv, ha⟩ := invLift2 hP L a0 (fun c d s hs => hLt c d rfl s hs) fun c d s hs => by
    have e1 : ev2 E1 E2 a0 s = φ ⟨s, hs⟩ := ha0 ⟨s, hs⟩
    have e2 : ev2 E1 E2 a0 ((E1 c d + E2 c d) s) = φ (EL c d ⟨s, hs⟩) := by
      have := ha0 (EL c d ⟨s, hs⟩)
      rw [hEL] at this
      exact this
    rw [e1, e2, hφ c d rfl]
    rfl
  refine ⟨a, hinv, ?_⟩
  rw [ha v hvL]
  exact (ha0 ⟨v, hvL⟩).trans hφv

end GlobalTheory.CompanionTheory.RealMult.Lift
