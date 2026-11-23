import Mathlib
import Formalism.FormalDegreeBessel.StatementIO
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

open Matrix
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CapelliCentral

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : _root_.Formalism.REAL.SmoothOnGV ε f) (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → f' g = f g) : _root_.Formalism.REAL.SmoothOnGV ε f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgG => (h g hgG).trans (hfF g hg hgG)⟩

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.smooth_add_smul {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : _root_.Formalism.REAL.SmoothOnGV ε f)
    (hf' : _root_.Formalism.REAL.SmoothOnGV ε f') (c : ℂ) : _root_.Formalism.REAL.SmoothOnGV ε (fun x => f x + c • f' x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c),
    fun g hg hgG => ?_⟩
  show f g + c • f' g = F g + c • F' g
  rw [hfF g hg.1 hgG, hfF' g hg.2 hgG]

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.smooth_zero :
    _root_.Formalism.REAL.SmoothOnGV ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.eab_smooth {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : _root_.Formalism.REAL.SmoothOnGV ε f) (a b : Fin n) : _root_.Formalism.REAL.SmoothOnGV ε (_root_.Formalism.REAL.EabV ε a b f) := by
  obtain ⟨hP, hQ, -, -⟩ := _root_.Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have h1 := _root_.Formalism.REAL.rdSmoothV n ε E f _ hf hP
  have h2 := _root_.Formalism.REAL.rdSmoothV n ε E f _ hf hQ
  have h3 := _root_.GlobalTheory.CapelliCentral.smooth_add_smul h1 h2 Complex.I
  exact _root_.GlobalTheory.CapelliCentral.smooth_congr h3 (fun g _ => rfl)

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.eab_add_smul {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : _root_.Formalism.REAL.SmoothOnGV ε f) (hf' : _root_.Formalism.REAL.SmoothOnGV ε f') (c : ℂ) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    _root_.Formalism.REAL.EabV ε a b (fun x => f x + c • f' x) g = _root_.Formalism.REAL.EabV ε a b f g + c • _root_.Formalism.REAL.EabV ε a b f' g := by
  obtain ⟨hP, hQ, -, -⟩ := _root_.Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have e1 := (_root_.Formalism.REAL.rdLinV n ε E f f' _ _ 0 c g hf hf' hP hP hg).2.2
  have e2 := (_root_.Formalism.REAL.rdLinV n ε E f f' _ _ 0 c g hf hf' hQ hQ hg).2.2
  show _root_.Formalism.REAL.EcV ε _ _ g = _root_.Formalism.REAL.EcV ε _ _ g + c • _root_.Formalism.REAL.EcV ε _ _ g
  unfold _root_.Formalism.REAL.EcV
  rw [e1, e2]
  simp only [smul_add, smul_comm Complex.I c]
  abel

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    _root_.Formalism.REAL.EabV ε a b (fun _ => (0 : E)) g = 0 := by
  simp [_root_.Formalism.REAL.EabV, _root_.Formalism.REAL.EcV, _root_.Formalism.REAL.RdV]

open Classical in

def cut (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => if inUJ ε g then f g else 0

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.cut_of_mem (f : Matrix (Fin n) (Fin n) ℂ → E)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    _root_.GlobalTheory.CapelliCentral.cut ε f g = f g := by
  unfold _root_.GlobalTheory.CapelliCentral.cut
  rw [if_pos hg]

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.cut_of_not_mem (f : Matrix (Fin n) (Fin n) ℂ → E)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : ¬ _root_.Formalism.REAL.inUJ ε g) :
    _root_.GlobalTheory.CapelliCentral.cut ε f g = 0 := by
  unfold _root_.GlobalTheory.CapelliCentral.cut
  rw [if_neg hg]

def smoothSpace (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → E) where
  carrier := {f | SmoothOnGV ε f ∧ ∀ g, ¬ inUJ ε g → f g = 0}
  zero_mem' := ⟨smooth_zero, fun _ _ => rfl⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨smooth_congr (smooth_add_smul h1 h3 1) (fun g _ => by simp), fun g hg => ?_⟩
    simp [h2 g hg, h4 g hg]
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨smooth_congr (smooth_add_smul smooth_zero h1 c) (fun g _ => by simp), fun g hg => ?_⟩
    simp [h2 g hg]

def mk (f : Matrix (Fin n) (Fin n) ℂ → E) (hf : SmoothOnGV ε f) : smoothSpace ε E :=
  ⟨cut ε f, smooth_congr hf (fun _ hg => cut_of_mem f hg), fun _ hg => cut_of_not_mem f hg⟩

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.mk_apply (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : _root_.Formalism.REAL.SmoothOnGV ε f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    (_root_.GlobalTheory.CapelliCentral.mk f hf).1 g = f g :=
  _root_.GlobalTheory.CapelliCentral.cut_of_mem f hg

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.ext_on {F F' : _root_.GlobalTheory.CapelliCentral.smoothSpace ε E}
    (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → F.1 g = F'.1 g) : F = F' := by
  apply Subtype.ext
  funext g
  by_cases hg : _root_.Formalism.REAL.inUJ ε g
  · exact h g hg
  · rw [F.2.2 g hg, F'.2.2 g hg]

def eabEnd (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : Fin n) :
    Module.End ℂ (smoothSpace ε E) where
  toFun F := mk (EabV ε a b F.1) (eab_smooth F.2.1 a b)
  map_add' F F' := by
    apply ext_on
    intro g hg
    have := eab_add_smul F.2.1 F'.2.1 1 a b hg
    simp only [one_smul] at this
    rw [mk_apply _ _ hg, Submodule.coe_add, Submodule.coe_add, Pi.add_apply, mk_apply _ _ hg,
      mk_apply _ _ hg]
    exact this
  map_smul' c F := by
    apply ext_on
    intro g hg
    have := eab_add_smul smooth_zero F.2.1 c a b hg
    simp only [zero_add, eab_zero] at this
    rw [mk_apply _ _ hg, Submodule.coe_smul, Submodule.coe_smul, Pi.smul_apply, mk_apply _ _ hg]
    exact this

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem inUJ_mul_foundation {g k : Matrix (Fin n) (Fin n) ℂ}
    (hg : _root_.Formalism.REAL.inUJ ε g) (hk : _root_.Formalism.REAL.inUJ ε k) : _root_.Formalism.REAL.inUJ ε (g * k) := by
  unfold _root_.Formalism.REAL.inUJ at *
  rw [conjTranspose_mul,
    show kᴴ * gᴴ * _root_.Formalism.REAL.Jm ε * (g * k) = kᴴ * (gᴴ * _root_.Formalism.REAL.Jm ε * g) * k by
      simp only [Matrix.mul_assoc], hg, hk]

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
private theorem rdV_congr_of_eqOn_inUJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : _root_.Formalism.REAL.inG ε X)
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → f g = f' g)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) : _root_.Formalism.REAL.RdV X f g = _root_.Formalism.REAL.RdV X f' g := by
  unfold _root_.Formalism.REAL.RdV
  congr 1
  funext t
  exact h _ (inUJ_mul_foundation hg (_root_.Formalism.REAL.f1alg_exp_inUJ ε _ (_root_.Formalism.REAL.lie_algebra_real_smul_mem ε hX t)))

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.eabEnd_apply (a b : Fin n) (F : _root_.GlobalTheory.CapelliCentral.smoothSpace ε E)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → F.1 g = f g)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    (_root_.GlobalTheory.CapelliCentral.eabEnd ε E a b F).1 g = _root_.Formalism.REAL.EabV ε a b f g := by
  obtain ⟨hP, hQ, -, -⟩ := _root_.Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  show _root_.GlobalTheory.CapelliCentral.cut ε (_root_.Formalism.REAL.EabV ε a b F.1) g = _
  rw [_root_.GlobalTheory.CapelliCentral.cut_of_mem _ hg]
  show _root_.Formalism.REAL.EcV ε _ _ g = _root_.Formalism.REAL.EcV ε _ _ g
  unfold _root_.Formalism.REAL.EcV
  rw [rdV_congr_of_eqOn_inUJ hP h hg, rdV_congr_of_eqOn_inUJ hQ h hg]

open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.eabEnd_glRel : _root_.Formalism.REAL.GlRel (_root_.GlobalTheory.CapelliCentral.eabEnd ε E) := by
  intro a b c d
  refine LinearMap.ext fun F => ?_
  apply _root_.GlobalTheory.CapelliCentral.ext_on
  intro g hg
  have hF : ∀ (p q : Fin n) (G : _root_.GlobalTheory.CapelliCentral.smoothSpace ε E),
      (_root_.GlobalTheory.CapelliCentral.eabEnd ε E p q G).1 g = _root_.Formalism.REAL.EabV ε p q G.1 g :=
    fun p q G => _root_.GlobalTheory.CapelliCentral.eabEnd_apply p q G (fun _ _ => rfl) hg
  have hFF : ∀ p q r s : Fin n,
      (_root_.GlobalTheory.CapelliCentral.eabEnd ε E p q (_root_.GlobalTheory.CapelliCentral.eabEnd ε E r s F)).1 g =
        _root_.Formalism.REAL.EabV ε p q (_root_.Formalism.REAL.EabV ε r s F.1) g :=
    fun p q r s => _root_.GlobalTheory.CapelliCentral.eabEnd_apply p q _
      (fun _ hg' => _root_.GlobalTheory.CapelliCentral.eabEnd_apply r s F (fun _ _ => rfl) hg') hg
  have key := _root_.Formalism.REAL.eabGlV n ε E F.1 a b c d g F.2.1 hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, hFF]
  rw [key]
  split_ifs <;> simp [hF]

lemma tm_apply (u : ℂ) (a b : Fin n) (F : smoothSpace ε E) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (h : ∀ g, inUJ ε g → F.1 g = f g) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (Tm (eabEnd ε E) u a b F).1 g = Top (EabV ε) u a b f g := by
  unfold Tm Formalism.QuantumDeterminants.Top
  rw [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, eabEnd_apply a b F h hg, ← h g hg]
  split_ifs <;> simp

lemma prod_apply (l : List (ℂ × Fin n × Fin n)) (F : smoothSpace ε E)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → F.1 g = f g) :
    ∀ g, inUJ ε g → ((l.map fun p => Tm (eabEnd ε E) p.1 p.2.1 p.2.2).prod F).1 g =
      (l.map fun p => Top (EabV ε) p.1 p.2.1 p.2.2).foldr (fun T h => T h) f g := by
  induction l with
  | nil => intro g hg; simpa using h g hg
  | cons p l ih =>
    intro g hg
    rw [List.map_cons, List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
    exact tm_apply _ _ _ _ ih hg

end GlobalTheory.CapelliCentral

namespace GlobalTheory

open Formalism.REAL Formalism.QuantumDeterminants CapelliCentral

end GlobalTheory
