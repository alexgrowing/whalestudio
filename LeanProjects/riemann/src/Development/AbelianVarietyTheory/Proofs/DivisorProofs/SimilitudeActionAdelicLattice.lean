import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdeleLimitCompatibleIntSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleAwayFromPEqZeroOfDivisibleCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseAdeleAwayFromPOfUnitCongruencesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDivisibleInLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicEndomorphismLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleInverseSystemLatticeMapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupAlgebraActionOfCommuteOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGroupAlgebraActionInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfPairingVanishes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingAdjointInvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingIntegral
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AdelicSim

variable {p : ℕ} [Fact p.Prime]

abbrev formAf (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (D.EF.baseChange ℚ).baseChange (AfP p)

theorem lim (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) :
    ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p →
      ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := GlobalTheory.T.exists_integralAdeleLimit_compatibleIntSystem p a ha

theorem zero (p : ℕ) [Fact p.Prime] (α : AfP p)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) : α = 0 := GlobalTheory.T.finiteAdeleAwayFromP_eq_zero_of_divisible_coprime p α h

theorem unit (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) :
    ∃ c' : AfP p, c * c' = 1 := GlobalTheory.T.exists_inverse_adeleAwayFromP_of_unitCongruences p c u h

theorem modZero (D : Datum p) (z : AfP p ⊗[ℚ] VQ D)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) : z = 0 := GlobalTheory.T.eq_zero_of_divisible_in_lattice p D z h

theorem modLim (D : Datum p) (g : ℕ → D.La →+ D.La)
    (hg : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) :
    ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := GlobalTheory.T.exists_adelic_endomorphism_lattice p D g hg

theorem invSys (D : Datum p) (g : ℕ → D.La →+ D.La)
    (hg : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z)
    (hsurj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z)
    (hinj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w) :
    ∃ g' : ℕ → D.La →+ D.La,
      (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g' (n * m) x = g' n x + n • z) ∧
      (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z) ∧
      (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g' n (g n x) = x + n • z) := GlobalTheory.T.exists_compatible_inverseSystem_latticeMaps p D g hg hsurj hinj

theorem comm {D : Datum p} {G : HTGroup p} (L : Link D G) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
    (hA : ∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) :
    ∃ y, actOn L.rep (AfP p) y = A := GlobalTheory.T.exists_groupAlgebra_action_of_commute_order p D G L A hA

theorem inj {D : Datum p} {G : HTGroup p} (L : Link D G) : Function.Injective (actOn L.rep (AfP p)) := GlobalTheory.T.adelicGroupAlgebraAction_injective p D G L

theorem nondeg (D : Datum p) (z : AfP p ⊗[ℚ] VQ D) (h : ∀ v, formAf D v z = 0) : z = 0 := GlobalTheory.T.eq_zero_of_pairing_vanishes p D z h

theorem adjAf {D : Datum p} {G : HTGroup p} (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D) :
    formAf D (actOn L.rep (AfP p) x v) w =
      formAf D v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := GlobalTheory.T.pairing_adjoint_involution p D G L x v w

theorem formInt (D : Datum p) {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    IsIntAf (formAf D v w) := GlobalTheory.T.lattice_pairing_integral p D _ _ hv hw

theorem isInt_one : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _

theorem isInt_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

def inAfHom (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D :=
  ((TensorProduct.mk ℚ (AfP p) (VQ D) 1).toAddMonoidHom).comp ((TensorProduct.mk ℤ ℚ D.La 1).toAddMonoidHom)

theorem inAf_eq (D : Datum p) (x : D.La) : inAf D x = inAfHom D x := rfl

theorem inAf_add (D : Datum p) (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := by
  simp only [inAf_eq, map_add]

theorem inAf_nsmul (D : Datum p) (n : ℕ) (x : D.La) : inAf D (n • x) = n • inAf D x := by
  simp only [inAf_eq, map_nsmul]

theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isInt_one, rfl⟩

theorem smul_mem_laHat (D : Datum p) {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', x, ha', rfl⟩ := hz
    rw [TensorProduct.smul_tmul']
    exact AddSubgroup.subset_closure ⟨a • a', x, isInt_mul ha ha', rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem span_inAf (D : Datum p) : Submodule.span (AfP p) (Set.range (inAf D)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a m =>
    have : (1 : AfP p) ⊗ₜ[ℚ] m ∈ Submodule.span (AfP p) (Set.range (inAf D)) := by
      induction m using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
      | tmul q x =>
        have e : (1 : AfP p) ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] x : VQ D) = q • inAf D x := by
          rw [inAf, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [e]
        exact Submodule.smul_of_tower_mem _ q (Submodule.subset_span ⟨x, rfl⟩)
    have e : a ⊗ₜ[ℚ] m = a • ((1 : AfP p) ⊗ₜ[ℚ] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e]; exact Submodule.smul_mem _ a this

theorem ext_inAf (D : Datum p) {f g : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)}
    (h : ∀ x, f (inAf D x) = g (inAf D x)) : f = g :=
  LinearMap.ext_on (span_inAf D) (by rintro _ ⟨x, rfl⟩; exact h x)

theorem bilinear_ext_adelic_inclusion (D : Datum p) {f g : AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p}
    (h : ∀ x y, f (inAf D x) (inAf D y) = g (inAf D x) (inAf D y)) : f = g :=
  LinearMap.ext_on (span_inAf D) (by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.ext_on (span_inAf D) (by rintro _ ⟨y, rfl⟩; exact h x y))

theorem bc_inAf (D : Datum p) (b : D.O) (x : D.La) :
    (actQ D b).baseChange (AfP p) (inAf D x) = inAf D (b • x) := by
  simp only [inAf, actQ, LinearMap.baseChange_tmul]; rfl

theorem bc_mem (D : Datum p) (b : D.O) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    (actQ D b).baseChange (AfP p) v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, b • x, ha, ?_⟩
    simp only [actQ, LinearMap.baseChange_tmul]; rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem form_inAf (D : Datum p) (x y : D.La) : formAf D (inAf D x) (inAf D y) = (D.EF x y : AfP p) := by
  simp [formAf, inAf, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

theorem congOne_of (D : Datum p) (f : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) (N : ℕ)
    (h : ∀ x, ∃ w ∈ LaHat D, f (inAf D x) = inAf D x + N • w) :
    ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, f v = v + N • w := by
  intro v hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := h x
    have ez : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = a • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    refine ⟨a • w, smul_mem_laHat D ha hw, ?_⟩
    rw [ez, map_smul, e, smul_add, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, e⟩ := hx
    obtain ⟨w', hw', e'⟩ := hy
    exact ⟨w + w', add_mem hw hw', by rw [map_add, e, e', smul_add]; abel⟩
  | neg x _ hx =>
    obtain ⟨w, hw, e⟩ := hx
    exact ⟨-w, neg_mem hw, by rw [map_neg, e, smul_neg, neg_add]⟩

theorem isInt_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isInt_sub {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem isInt_intCast (k : ℤ) : IsIntAf (k : AfP p) := fun v => by rw [map_intCast]; exact intCast_mem _ k

theorem isInt_nsmul {a : AfP p} (ha : IsIntAf a) (n : ℕ) : IsIntAf (n • a) := fun v => by
  rw [map_nsmul]; exact nsmul_mem (ha v) n

theorem exists_mem_KN (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ)
    (hN : 0 < N) (hNp : N.Coprime p) (t : SimSys D N N) :
    ∃ h ∈ L.KN N, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x : D.La, ∃ w ∈ LaHat D,
      L.actG h (inAf D x) = inAf D (t.g n x) + n • w := by
  classical
  obtain ⟨g', htw', hgg', hg'g⟩ := invSys D t.g t.tower t.surj t.inj
  obtain ⟨h₀, h₀L, h₀c⟩ := modLim D t.g t.tower
  obtain ⟨h₁, h₁L, h₁c⟩ := modLim D g' htw'
  have inv_of : ∀ (f₀ f₁ : ℕ → D.La →+ D.La) (k₀ k₁ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)),
      (∀ v ∈ LaHat D, k₀ v ∈ LaHat D) →
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, k₀ (inAf D x) = inAf D (f₀ n x) + n • w) →
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, k₁ (inAf D x) = inAf D (f₁ n x) + n • w) →
      (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, f₀ n (f₁ n x) = x + n • z) → k₀ * k₁ = 1 := by
    intro f₀ f₁ k₀ k₁ hk₀L hk₀ hk₁ hf
    refine ext_inAf D fun x => ?_
    have := modZero D ((k₀ * k₁) (inAf D x) - inAf D x) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := hk₁ n hn hc x
      obtain ⟨w', hw', e'⟩ := hk₀ n hn hc (f₁ n x)
      obtain ⟨z, hz⟩ := hf n hn hc x
      refine ⟨inAf D z + w' + k₀ w, add_mem (add_mem (inAf_mem D z) hw') (hk₀L w hw), ?_⟩
      rw [Module.End.mul_apply, e, map_add, e', hz, inAf_add, inAf_nsmul, map_nsmul]
      simp only [smul_add]; abel
    rw [Module.End.one_apply]; exact sub_eq_zero.1 this
  have e01 : h₀ * h₁ = 1 := inv_of t.g g' h₀ h₁ h₀L h₀c h₁c hgg'
  have e10 : h₁ * h₀ = 1 := inv_of g' t.g h₁ h₀ h₁L h₁c h₀c hg'g
  have c0 : ∀ b : D.O, h₀ * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * h₀ := by
    intro b
    refine ext_inAf D fun x => ?_
    have := modZero D ((h₀ * (actQ D b).baseChange (AfP p)) (inAf D x) -
        ((actQ D b).baseChange (AfP p) * h₀) (inAf D x)) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := h₀c n hn hc (b • x)
      obtain ⟨w', hw', e'⟩ := h₀c n hn hc x
      obtain ⟨z, hz⟩ := t.lin n hn hc b x
      refine ⟨inAf D z + w - (actQ D b).baseChange (AfP p) w',
        sub_mem (add_mem (inAf_mem D z) hw) (bc_mem D b hw'), ?_⟩
      rw [Module.End.mul_apply, Module.End.mul_apply, bc_inAf, e, hz, e', map_add, bc_inAf, map_nsmul, inAf_add,
        inAf_nsmul]
      simp only [smul_add, smul_sub]; abel
    exact sub_eq_zero.1 this
  have c1 : ∀ b : D.O, h₁ * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * h₁ := by
    intro b
    calc h₁ * (actQ D b).baseChange (AfP p) = h₁ * ((actQ D b).baseChange (AfP p) * h₀) * h₁ := by
          rw [_root_.mul_assoc h₁, _root_.mul_assoc ((actQ D b).baseChange (AfP p)), e01, _root_.mul_one]
      _ = h₁ * (h₀ * (actQ D b).baseChange (AfP p)) * h₁ := by rw [c0]
      _ = _ := by rw [← _root_.mul_assoc h₁ h₀, e10, _root_.one_mul]
  obtain ⟨y, hy⟩ := comm L h₀ c0
  obtain ⟨y', hy'⟩ := comm L h₁ c1
  have yy' : y * y' = 1 := inj L (by rw [map_mul, hy, hy', e01, map_one])
  have y'y : y' * y = 1 := inj L (by rw [map_mul, hy, hy', e10, map_one])
  obtain ⟨c, hcI, hc⟩ := lim p (fun n => (t.u n : ℤ)) fun n m hn hm hnm => (t.u_tower n m hn hm hnm).symm.dvd
  obtain ⟨c', hcc'⟩ := unit p c t.u fun n hn hnp => ⟨t.u_cop n hn hnp, by
    obtain ⟨β, hβ, e⟩ := hc n hn hnp
    exact ⟨β, hβ, by rw [e, Int.cast_natCast]⟩⟩
  have key : ∀ x x', formAf D (h₀ (inAf D x)) (h₀ (inAf D x')) = c * formAf D (inAf D x) (inAf D x') := by
    intro x x'
    have := zero p (formAf D (h₀ (inAf D x)) (h₀ (inAf D x')) - c * formAf D (inAf D x) (inAf D x'))
      fun n hn hnp => by
      obtain ⟨w, hw, e⟩ := h₀c n hn hnp x
      obtain ⟨w', hw', e'⟩ := h₀c n hn hnp x'
      obtain ⟨β, hβ, eβ⟩ := hc n hn hnp
      obtain ⟨k, hk⟩ := t.sim n hn hnp x x'
      refine ⟨(k : AfP p) + formAf D (inAf D (t.g n x)) w' + formAf D w (inAf D (t.g n x')) +
        n • formAf D w w' - β * (D.EF x x' : AfP p), ?_, ?_⟩
      · exact isInt_sub (isInt_add (isInt_add (isInt_add (isInt_intCast k)
          (formInt D (inAf_mem D _) hw')) (formInt D hw (inAf_mem D _))) (isInt_nsmul (formInt D hw hw') n))
          (isInt_mul hβ (isInt_intCast _))
      · have hk' := congrArg (Int.cast : ℤ → AfP p) hk
        push_cast at hk'
        rw [e, e', eβ]
        simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, form_inAf, nsmul_eq_mul]
        push_cast
        linear_combination hk'
    exact sub_eq_zero.1 this
  have hsim : ∀ v w, formAf D (h₀ v) (h₀ w) = c * formAf D v w := by
    have e2 := bilinear_ext_adelic_inclusion D (f := (formAf D).compl₁₂ h₀ h₀) (g := c • formAf D) fun x x' => by
      simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul]; exact key x x'
    intro v w
    have := LinearMap.congr_fun₂ e2 v w
    simpa using this
  set s := (starT G.star (AfP p) y).unop with hsdef
  have hs : s * y = algebraMap (AfP p) _ c := by
    apply inj L
    refine LinearMap.ext fun w => sub_eq_zero.1 (nondeg D _ fun v => ?_)
    rw [map_sub, map_mul, Module.End.mul_apply, hy, AlgHom.commutes, Module.algebraMap_end_apply, hsdef,
      ← adjAf L y v (h₀ w), hy, hsim, map_smul, smul_eq_mul, sub_self]
  have hys : y * s = algebraMap (AfP p) _ c := by
    calc y * s = y * s * (y * y') := by rw [yy', _root_.mul_one]
      _ = y * (s * y) * y' := by simp only [_root_.mul_assoc]
      _ = y * algebraMap (AfP p) _ c * y' := by rw [hs]
      _ = algebraMap (AfP p) _ c * (y * y') := by rw [(Algebra.commutes c y).symm, _root_.mul_assoc]
      _ = _ := by rw [yy', _root_.mul_one]
  let yU : (AfP p ⊗[ℚ] G.C)ˣ := ⟨y, y', yy', y'y⟩
  let cU : (AfP p)ˣ := ⟨c, c', hcc', by rw [mul_comm]; exact hcc'⟩
  have hmem : (yU, cU) ∈ UPts G.star (AfP p) := mem_uGroup.2 hys
  let h : G.GAf := ⟨(yU, cU), hmem⟩
  have ha0 : L.actG h = h₀ := hy
  have ha1 : L.actG h⁻¹ = h₁ := hy'
  refine ⟨h, ⟨?_, ?_⟩, fun n hn hnp x => ?_⟩
  · intro v hv
    rw [ha0]
    refine congOne_of D h₀ N (fun x => ?_) v hv
    obtain ⟨w, hw, e⟩ := h₀c N hN hNp x
    obtain ⟨z, hz⟩ := t.one x
    exact ⟨inAf D z + w, add_mem (inAf_mem D z) hw, by rw [e, hz, inAf_add, inAf_nsmul, smul_add, add_assoc]⟩
  · intro v hv
    rw [ha1]
    refine congOne_of D h₁ N (fun x => ?_) v hv
    obtain ⟨w, hw, e⟩ := h₁c N hN hNp x
    obtain ⟨z₁, hz₁⟩ := hgg' N hN hNp x
    obtain ⟨z₂, hz₂⟩ := t.one (g' N x)
    have hx : g' N x = x + N • (z₁ - z₂) := by
      rw [hz₂] at hz₁
      rw [smul_sub, ← add_sub_assoc, ← hz₁, add_sub_cancel_right]
    exact ⟨inAf D (z₁ - z₂) + w, add_mem (inAf_mem D _) hw,
      by rw [e, hx, inAf_add, inAf_nsmul, smul_add, add_assoc]⟩
  · rw [ha0]; exact h₀c n hn hnp x

end GlobalTheory.AdelicSim
