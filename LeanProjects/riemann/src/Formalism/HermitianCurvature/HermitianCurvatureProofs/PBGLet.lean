import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieDecompositionLocal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeadingTermIdentity
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def PolyRepN (d : ℕ) (f : ℂ → E) (top : E) : Prop :=
  ∃ c : ℕ → E, c d = top ∧ ∀ u, f u = ∑ l ∈ range (d + 1), u ^ l • c l

theorem polyRepN_smul {d : ℕ} {f : ℂ → E} {top : E} (h : PolyRepN d f top) (s : ℂ) :
    PolyRepN d (fun u => s • f u) (s • top) := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun l => s • c l, by beta_reduce; rw [hc], fun u => ?_⟩
  beta_reduce
  rw [hf u, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_comm]

theorem polyRepN_mono {d d' : ℕ} (hdd : d ≤ d') {f : ℂ → E} {top : E} (h : PolyRepN d f top) :
    PolyRepN d' f (if d = d' then top else 0) := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun l => if l ≤ d then c l else 0, ?_, fun u => ?_⟩
  · beta_reduce
    by_cases e : d = d'
    · subst e; simp [hc]
    · rw [if_neg (by omega), if_neg e]
  · beta_reduce
    rw [hf u]
    symm
    rw [← Finset.sum_subset (fun x hx => by simp at hx ⊢; omega : range (d + 1) ⊆ range (d' + 1))]
    · apply Finset.sum_congr rfl
      intro l hl
      rw [if_pos (by simp at hl; omega)]
    · intro l _ hl
      rw [if_neg (by simp at hl; omega), smul_zero]

theorem polyRepN_shift {d : ℕ} {f : ℂ → E} {top : E} (h : PolyRepN d f top) (a : ℂ) :
    PolyRepN d (fun Y => f (Y + a)) top := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun i => ∑ l ∈ range (d + 1), (a ^ (l - i) * (Nat.choose l i : ℂ)) • c l, ?_, fun Y => ?_⟩
  · beta_reduce
    rw [Finset.sum_eq_single d]
    · simp [hc]
    · intro l hl hne
      simp at hl
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · intro h; simp at h
  · beta_reduce
    rw [hf (Y + a)]
    have e1 : ∀ l ∈ range (d + 1), (Y + a) ^ l • c l =
        ∑ i ∈ range (d + 1), (Y ^ i * (a ^ (l - i) * (Nat.choose l i : ℂ))) • c l := by
      intro l hl
      simp at hl
      rw [add_pow, Finset.sum_smul]
      rw [← Finset.sum_subset (fun x hx => by simp at hx ⊢; omega : range (l + 1) ⊆ range (d + 1))]
      · apply Finset.sum_congr rfl
        intro i _
        congr 1
        ring
      · intro i _ hi
        simp at hi
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [Finset.sum_congr rfl e1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [smul_smul]

end poly

section ops

open Classical

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem loc_zero' (g : Mat k r) : Loc (⊤ : ℕ∞) (fun _ : Mat k r => (0 : E)) g :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem loc_of_eq {m : ℕ∞} {f f₂ : Mat k r → E} {g : Mat k r} (h : Loc m f g) {V : Set (Mat k r)}
    (hV : IsOpen V) (hg : g ∈ V) (he : ∀ x ∈ V, x ∈ GV k r → f₂ x = f x) : Loc m f₂ g := by
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := h
  exact ⟨U ∩ V, f', hU.inter hV, ⟨hgU, hg⟩, hf'.mono Set.inter_subset_left,
    fun x hx hxG => by rw [he x hx.2 hxG, hfe x hx.1 hxG]⟩

theorem hermitian_part_one_mem_lie (Z : Mat k r) : inLie k r (hpart1 (Hpk k r) Z) := Formalism.FourierDecayAlt.P.Qx2.hpart1_lie Z

theorem hermitian_part_two_mem_lie (Z : Mat k r) : inLie k r (hpart2 (Hpk k r) Z) := Formalism.FourierDecayAlt.P.Qx2.hpart2_lie Z

theorem eabH_loc (a b : Fin (2 * r + k + 1)) {f : Mat k r → E} {g : Mat k r} (h : Loc (⊤ : ℕ∞) f g) :
    Loc (⊤ : ℕ∞) (EabH (Hpk k r) a b f) g := by
  have h' : Loc ((⊤ : ℕ∞) + 1) f g := by rwa [top_add]
  exact loc_add (loc_RdV (hermitian_part_one_mem_lie _) h') (loc_RdV (hermitian_part_two_mem_lie _) h') Complex.I

theorem eabH_add (a b : Fin (2 * r + k + 1)) {f₁ f₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc 1 f₁ g)
    (h₂ : Loc 1 f₂ g) (hg : g ∈ GV k r) (c : ℂ) :
    EabH (Hpk k r) a b (fun x => f₁ x + c • f₂ x) g = EabH (Hpk k r) a b f₁ g + c • EabH (Hpk k r) a b f₂ g := by
  unfold EabH
  rw [Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_fun_add h₁ h₂ hg (hermitian_part_one_mem_lie _) c, Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_fun_add h₁ h₂ hg (hermitian_part_two_mem_lie _) c]
  module

theorem eabH_congr (a b : Fin (2 * r + k + 1)) {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    {g : Mat k r} (hg : g ∈ V) (hgG : g ∈ GV k r) (he : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) :
    EabH (Hpk k r) a b f₁ g = EabH (Hpk k r) a b f₂ g := by
  unfold EabH
  rw [rdV_congr hV hg hgG (hermitian_part_one_mem_lie _) he, rdV_congr hV hg hgG (hermitian_part_two_mem_lie _) he]

theorem eabH_zero (a b : Fin (2 * r + k + 1)) (g : Mat k r) :
    EabH (Hpk k r) a b (fun _ : Mat k r => (0 : E)) g = 0 := by
  simp [EabH, RdV]

def Wsm (U₀ : Set (Mat k r)) : Submodule ℂ (Mat k r → E) where
  carrier := {f | ∀ g ∈ U₀, g ∈ GV k r → Loc (⊤ : ℕ∞) f g}
  add_mem' := by
    intro f₁ f₂ h₁ h₂ g hg hgG
    have := loc_add (h₁ g hg hgG) (h₂ g hg hgG) 1
    convert this using 1
    funext x; simp
  zero_mem' := fun g _ _ => loc_zero' g
  smul_mem' := by
    intro c f hf g hg hgG
    have := loc_add (loc_zero' (E := E) g) (hf g hg hgG) c
    convert this using 1
    funext x; simp

theorem loc1 {f : Mat k r → E} {g : Mat k r} (h : Loc (⊤ : ℕ∞) f g) : Loc 1 f g := loc_mono le_top h

def EHt (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀) (a b : Fin (2 * r + k + 1)) :
    Wsm (E := E) U₀ →ₗ[ℂ] Wsm (E := E) U₀ where
  toFun f := ⟨fun g => if g ∈ U₀ ∧ g ∈ GV k r then EabH (Hpk k r) a b f.1 g else 0, by
    intro g hg hgG
    exact loc_of_eq (eabH_loc a b (f.2 g hg hgG)) hU₀ hg (fun x hx hxG => by simp [hx, hxG])⟩
  map_add' f₁ f₂ := by
    refine Subtype.ext (funext fun g => ?_)
    simp only [Submodule.coe_add, Pi.add_apply]
    split_ifs with hS
    · have e : ((f₁ : Mat k r → E) + f₂) = fun x => f₁.1 x + (1 : ℂ) • f₂.1 x := by funext x; simp
      rw [e, eabH_add a b (loc1 (f₁.2 g hS.1 hS.2)) (loc1 (f₂.2 g hS.1 hS.2)) hS.2, one_smul]
    · simp
  map_smul' c f := by
    refine Subtype.ext (funext fun g => ?_)
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    split_ifs with hS
    · have e : (c • (f : Mat k r → E)) = fun x => (fun _ : Mat k r => (0 : E)) x + c • f.1 x := by
        funext x; simp
      rw [e, eabH_add a b (loc1 (loc_zero' g)) (loc1 (f.2 g hS.1 hS.2)) hS.2, eabH_zero, zero_add]
    · simp

variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)

theorem top_agree (u : ℂ) (a b : Fin (2 * r + k + 1)) (h : Wsm (E := E) U₀) (g : Mat k r) (hg : g ∈ U₀)
    (hgG : g ∈ GV k r) :
    ((Tm (fun a b => EHt (E := E) U₀ hU₀ a b) u a b) h).1 g = QuantumDeterminants.Top (EabH (Hpk k r)) u a b h.1 g := by
  unfold Tm QuantumDeterminants.Top
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  congr 1
  · split_ifs
    · simp [Module.algebraMap_end_apply]
    · simp
  · show (if g ∈ U₀ ∧ g ∈ GV k r then _ else _) = _
    rw [if_pos ⟨hg, hgG⟩]

include hU₀ in
theorem top_congr' (u : ℂ) (a b : Fin (2 * r + k + 1)) {h₁ h₂ : Mat k r → E}
    (he : ∀ x ∈ U₀, x ∈ GV k r → h₁ x = h₂ x) (g : Mat k r) (hg : g ∈ U₀) (hgG : g ∈ GV k r) :
    Top (EabH (Hpk k r)) u a b h₁ g = QuantumDeterminants.Top (EabH (Hpk k r)) u a b h₂ g := by
  unfold QuantumDeterminants.Top
  rw [he g hg hgG, eabH_congr a b hU₀ hg hgG he]

theorem fold_agree : ∀ (L : List (Module.End ℂ (Wsm (E := E) U₀) × ((Mat k r → E) → (Mat k r → E)))),
    (∀ p ∈ L, ∀ (h : Wsm (E := E) U₀), ∀ g ∈ U₀, g ∈ GV k r → (p.1 h).1 g = p.2 h.1 g) →
    (∀ p ∈ L, ∀ (h₁ h₂ : Mat k r → E), (∀ x ∈ U₀, x ∈ GV k r → h₁ x = h₂ x) →
      ∀ g ∈ U₀, g ∈ GV k r → p.2 h₁ g = p.2 h₂ g) →
    ∀ (f : Wsm (E := E) U₀), ∀ g ∈ U₀, g ∈ GV k r →
      ((L.map Prod.fst).prod f).1 g = (L.map Prod.snd).foldr (fun T h => T h) f.1 g
  | [], _, _, f, g, _, _ => by simp
  | p :: L, hA, hC, f, g, hg, hgG => by
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
    rw [hA p (by simp) _ g hg hgG]
    apply hC p (by simp) _ _ _ g hg hgG
    intro x hx hxG
    exact fold_agree L (fun q hq => hA q (by simp [hq])) (fun q hq => hC q (by simp [hq])) f x hx hxG

theorem qminor_agree {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Wsm (E := E) U₀) (g : Mat k r)
    (hg : g ∈ U₀) (hgG : g ∈ GV k r) :
    ((qminor (fun a b => EHt (E := E) U₀ hU₀ a b) a b u) f).1 g = qminorOp (EabH (Hpk k r)) a b u f.1 g := by
  unfold qminor qminorOp
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Module.End.mul_apply]
  have hL := fold_agree U₀ (List.ofFn fun i : Fin t =>
      (Tm (fun a b => EHt (E := E) U₀ hU₀ a b) (u - ((i : ℕ) : ℂ)) (a (σ i)) (b i),
        QuantumDeterminants.Top (EabH (Hpk k r)) (u - ((i : ℕ) : ℂ)) (a (σ i)) (b i)))
    (by
      intro p hp h x hx hxG
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp
      exact top_agree U₀ hU₀ _ _ _ h x hx hxG)
    (by
      intro p hp h₁ h₂ he x hx hxG
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hp
      exact top_congr' U₀ hU₀ _ _ _ he x hx hxG)
    f g hg hgG
  rw [List.map_ofFn, List.map_ofFn] at hL
  simp only [Function.comp_def] at hL
  rw [Pi.smul_apply]
  have hz : ∀ (z : ℤ) (v : Wsm (E := E) U₀), ((z : Module.End ℂ (Wsm (E := E) U₀)) v) = (z : ℂ) • v := by
    intro z v
    rw [Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  rw [hz, Submodule.coe_smul, Pi.smul_apply, hL]

end ops

section letters

open Classical

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def xi0 (g₀ : Mat k r) : Fin r → Fin (2 * r + k + 1) → ℂ :=
  fun a p => herm (Hpk k r) (g₀ *ᵥ bvec p) (bvec (eI k r a))

def y0 (g₀ : Mat k r) : Fin r → Fin (2 * r + k + 1) → ℂ :=
  fun a p => (g₀⁻¹ *ᵥ bvec (eI k r a)) p

variable (U₀ : Set (Mat k r)) (hU₀ : IsOpen U₀)

theorem AAop_eq (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    C3.AAop k r m hm u f.1 g₀ = ((C3.AAx k r (fun a b => EHt (E := E) U₀ hU₀ a b) (xi0 g₀) m hm u) f).1 g₀ := by
  unfold C3.AAop C3.AAx
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, qminor_agree U₀ hU₀ _ _ _ f g₀ hg hgG]
    rfl
  · simp

theorem AAvop_eq (m : ℕ) (hm : m ≤ r) (ell : ℂ) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    C3.AAvop k r m hm ell f.1 g₀ = ((C3.AAv k r (fun a b => EHt (E := E) U₀ hU₀ a b) (y0 g₀) m hm ell) f).1 g₀ := by
  unfold C3.AAvop C3.AAv
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, qminor_agree U₀ hU₀ _ _ _ f g₀ hg hgG]
    rfl
  · simp

include hU₀ in
theorem poly_AAop (m : ℕ) (hm : m ≤ r) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    PolyRepN m (fun u => C3.AAop k r m hm u f.1 g₀)
      ((Matrix.of fun a b : Fin m => xi0 g₀ (Fin.castLE hm a) (C3.xR k r m hm b)).det • f.1 g₀) := by
  obtain ⟨B, hB⟩ := Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity (Module.End ℂ (Wsm (E := E) U₀)) k r
    (fun a b => EHt (E := E) U₀ hU₀ a b) (xi0 g₀) m hm
  refine ⟨fun l => if h : l < m then (B ⟨l, h⟩ f).1 g₀ else
    (Matrix.of fun a b : Fin m => xi0 g₀ (Fin.castLE hm a) (C3.xR k r m hm b)).det • f.1 g₀, by simp, fun u => ?_⟩
  beta_reduce
  rw [AAop_eq U₀ hU₀ m hm u f g₀ hg hgG, hB u, Finset.sum_range_succ, dif_neg (lt_irrefl m)]
  simp only [LinearMap.add_apply, Module.algebraMap_end_apply, LinearMap.sum_apply, Module.End.mul_apply,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  rw [add_comm, Finset.sum_range (fun l => u ^ l • if h : l < m then (B ⟨l, h⟩ f).1 g₀ else _)]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    rw [dif_pos l.isLt]
  · rw [smul_smul]

include hU₀ in
theorem poly_AAvop (m : ℕ) (hm : m ≤ r) (f : Wsm (E := E) U₀) (g₀ : Mat k r) (hg : g₀ ∈ U₀)
    (hgG : g₀ ∈ GV k r) :
    PolyRepN m (fun ell => C3.AAvop k r m hm ell f.1 g₀)
      ((Matrix.of fun a b : Fin m => y0 g₀ (Fin.castLE hm a) (C3.sR k r m hm b)).det • f.1 g₀) := by
  obtain ⟨B, hB⟩ := Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_vector_identity (Module.End ℂ (Wsm (E := E) U₀)) k r
    (fun a b => EHt (E := E) U₀ hU₀ a b) (y0 g₀) m hm
  refine ⟨fun l => if h : l < m then (B ⟨l, h⟩ f).1 g₀ else
    (Matrix.of fun a b : Fin m => y0 g₀ (Fin.castLE hm a) (C3.sR k r m hm b)).det • f.1 g₀, by simp, fun u => ?_⟩
  beta_reduce
  rw [AAvop_eq U₀ hU₀ m hm u f g₀ hg hgG, hB u, Finset.sum_range_succ, dif_neg (lt_irrefl m)]
  simp only [LinearMap.add_apply, Module.algebraMap_end_apply, LinearMap.sum_apply, Module.End.mul_apply,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum, Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  rw [add_comm, Finset.sum_range (fun l => u ^ l • if h : l < m then (B ⟨l, h⟩ f).1 g₀ else _)]
  congr 1
  · apply Finset.sum_congr rfl
    intro l _
    rw [dif_pos l.isLt]
  · rw [smul_smul]

end letters

section final

open Classical

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem det_upper_minor_eq_minor (z z' : Fin (2 * r + k + 1) → ℂ) (g₀ : Mat k r) (m : ℕ) (hm : m ≤ r) :
    (Matrix.of fun a b : Fin m => xi0 g₀ (Fin.castLE hm a) (C3.xR k r m hm b)).det =
      Dmin k r z z' g₀ ⟨m, by omega⟩ := by
  unfold Dmin
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.submatrix_apply, Zhat, fvec, xi0, C3.xR]
  rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
  rfl

theorem det_lower_minor_eq_conj (z z' : Fin (2 * r + k + 1) → ℂ) (g₀ : Mat k r) (hg : g₀ ∈ GV k r) (m : ℕ) (hm : m ≤ r) :
    (Matrix.of fun a b : Fin m => y0 g₀ (Fin.castLE hm a) (C3.sR k r m hm b)).det =
      starRingEnd ℂ (Dmin k r z z' g₀ ⟨m, by omega⟩) := by
  unfold Dmin
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [Matrix.of_apply, y0, C3.sR]
  rw [(Formalism.FourierDecayAlt.P.SignAntidiagonal.xi_Y_zhat_identity k r z z' g₀ (Fin.castLE hm a) (Fin.castLE hm b) hg).2]
  rfl

theorem vLet_poly {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (G : B.Mat k r → E) (g₀ : B.Mat k r)
    (hg₀ : g₀ ∈ GV k r) (hD : Dmin k r z z' g₀ ⟨j, by omega⟩ ≠ 0) (hG : Loc (⊤ : ℕ∞) G g₀) (b : Bool) (e : Fin 2) :
    ∃ c : Fin (j + 1) → E, c (Fin.last j) = (if e = 0 then G g₀ else 0) ∧
      ∀ Y : ℝ, D.vLet k r z z' j hj (b, Y) e G g₀ = ∑ l : Fin (j + 1), ((Y : ℂ) ^ (l : ℕ)) • c l := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := hG
  have hW : G ∈ Wsm (E := E) U := fun g hg hgG => ⟨U, f', hU, hg, hf', he⟩
  set Gw : Wsm (E := E) U := ⟨G, hW⟩ with hGw
  by_cases h10 : e = 1 ∧ j = 0
  · refine ⟨fun _ => 0, ?_, fun Y => ?_⟩
    · rw [if_neg (by rw [h10.1]; decide)]
    · simp [D.vLet, if_pos h10]
  have hej : (e : ℕ) ≤ j := by
    rcases Fin.exists_fin_two.1 ⟨e, rfl⟩ with h | h <;> subst h <;> simp <;> omega
  have htop : ∀ (x : E), (if j - (e : ℕ) = j then x else 0) = (if e = 0 then x else 0) := by
    intro x
    rcases Fin.exists_fin_two.1 ⟨e, rfl⟩ with h | h <;> subst h
    · simp
    · have : j ≠ 0 := fun h0 => h10 ⟨rfl, h0⟩
      rw [if_neg (by simp; omega), if_neg (by decide)]
  cases b
  ·
    have P := polyRepN_mono (Nat.sub_le j e) (polyRepN_smul (polyRepN_shift
      (poly_AAvop U hU (j - e) (by omega) Gw g₀ hgU hg₀) (-(((2 * r + k : ℕ) : ℂ) / 2)))
      (starRingEnd ℂ (Dmin k r z z' g₀ ⟨j, by omega⟩))⁻¹)
    obtain ⟨c, hc, hf⟩ := P
    refine ⟨fun l : Fin (j + 1) => c l.val, ?_, fun Y => ?_⟩
    · simp only [Fin.val_last]
      rw [hc, htop]
      split_ifs with he0
      · subst he0
        have e2 : Dmin k r z z' g₀ ⟨j - ((0 : Fin 2) : ℕ), by omega⟩ = Dmin k r z z' g₀ ⟨j, by omega⟩ := rfl
        rw [det_lower_minor_eq_conj z z' g₀ hg₀, smul_smul, e2, inv_mul_cancel₀ ((map_ne_zero _).2 hD), one_smul]
      · rfl
    · simp only [D.vLet]
      rw [if_neg h10, if_neg (by simp)]
      have := hf (Y : ℂ)
      simp only at this
      rw [← sub_eq_add_neg] at this
      rw [this, Fin.sum_univ_eq_sum_range (fun l => ((Y : ℂ) ^ l) • c l)]
  ·
    have P := polyRepN_mono (Nat.sub_le j e) (polyRepN_smul (polyRepN_shift
      (poly_AAop U hU (j - e) (by omega) Gw g₀ hgU hg₀) (((2 * r + k : ℕ) : ℂ) / 2))
      (Dmin k r z z' g₀ ⟨j, by omega⟩)⁻¹)
    obtain ⟨c, hc, hf⟩ := P
    refine ⟨fun l : Fin (j + 1) => c l.val, ?_, fun Y => ?_⟩
    · simp only [Fin.val_last]
      rw [hc, htop]
      split_ifs with he0
      · subst he0
        have e2 : Dmin k r z z' g₀ ⟨j - ((0 : Fin 2) : ℕ), by omega⟩ = Dmin k r z z' g₀ ⟨j, by omega⟩ := rfl
        rw [det_upper_minor_eq_minor z z' g₀, smul_smul, e2, inv_mul_cancel₀ hD, one_smul]
      · rfl
    · simp only [D.vLet]
      rw [if_neg h10, if_pos (by simp)]
      have := hf (Y : ℂ)
      simp only at this
      rw [this, Fin.sum_univ_eq_sum_range (fun l => ((Y : ℂ) ^ l) • c l)]

end final

section smooth

open Classical

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

@[fun_prop] theorem contDiff_starC {n : WithTop ℕ∞} : ContDiff ℝ n (fun x : ℂ => star x) :=
  Complex.conjCLE.contDiff

theorem contDiff_det' {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (M : X → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i j, ContDiff ℝ ⊤ (fun x => M x i j)) :
    ContDiff ℝ ⊤ (fun x => (M x).det) := by
  simp only [Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod (fun i _ => h (σ i) i))

theorem contDiff_Dmin (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ContDiff ℝ ⊤ (fun g : Mat k r => Dmin k r z z' g l) := by
  unfold Dmin
  apply contDiff_det'
  intro a b
  simp only [Matrix.submatrix_apply, Zhat, herm, dotProduct, mulVec]
  fun_prop

theorem loc_smulFun {f : Mat k r → E} {g : Mat k r} (φ : Mat k r → ℂ) (hφ : ContDiff ℝ ⊤ φ)
    (h : Loc (⊤ : ℕ∞) f g) : Loc (⊤ : ℕ∞) (fun x => φ x • f x) g := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  exact ⟨U, fun x => φ x • f' x, hU, hgU, (hφ.of_le le_top).contDiffOn.smul hf', fun x hx hxG => by simp only [he x hx hxG]⟩

theorem loc_invsmul {f : Mat k r → E} {g : Mat k r} (φ : Mat k r → ℂ) (hφ : ContDiff ℝ ⊤ φ) (hg : φ g ≠ 0)
    (h : Loc (⊤ : ℕ∞) f g) : Loc (⊤ : ℕ∞) (fun x => (φ x)⁻¹ • f x) g := by
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h
  refine ⟨U ∩ {x | φ x ≠ 0}, fun x => (φ x)⁻¹ • f' x,
    hU.inter (isOpen_ne_fun hφ.continuous continuous_const), ⟨hgU, hg⟩, ?_,
    fun x hx hxG => by simp only [he x hx.1 hxG]⟩
  exact (((hφ.of_le le_top).contDiffOn).inv (fun x (hx : x ∈ U ∩ {x | φ x ≠ 0}) => hx.2)).smul
    (hf'.mono Set.inter_subset_left)

theorem loc_sum {ι : Type*} (s : Finset ι) (F : ι → Mat k r → E) {g : Mat k r}
    (h : ∀ i ∈ s, Loc (⊤ : ℕ∞) (F i) g) : Loc (⊤ : ℕ∞) (fun x => ∑ i ∈ s, F i x) g := by
  induction s using Finset.induction_on with
  | empty => simpa using loc_zero' (E := E) g
  | insert a s ha ih =>
    have := loc_add (h a (by simp)) (ih (fun i hi => h i (by simp [hi]))) 1
    convert this using 1
    funext x
    rw [Finset.sum_insert ha, one_smul]

theorem inv_GV {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1]; exact Formalism.QuantumDeterminants.GBasic.Hpk_sq k r

variable (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r)

def Sd : Set (Mat k r) := {g | Dmin k r z z' g ⟨j, by omega⟩ ≠ 0}

theorem isOpen_Sd : IsOpen (Sd z z' j hj) :=
  isOpen_ne_fun (contDiff_Dmin z z' _).continuous continuous_const

theorem vLet_mem (l : C.Letter) (e : Fin 2) (h : Wsm (E := E) (Sd z z' j hj)) :
    D.vLet k r z z' j hj l e h.1 ∈ Wsm (E := E) (Sd z z' j hj) := by
  intro g₀ hg hgG
  have hU₀ := isOpen_Sd z z' j hj
  by_cases h10 : e = 1 ∧ j = 0
  · have e0 : D.vLet k r z z' j hj l e h.1 = fun _ => 0 := by funext g; simp [D.vLet, if_pos h10]
    rw [e0]; exact loc_zero' g₀
  have hm : j - (e : ℕ) ≤ r := by omega
  rcases l with ⟨b, y⟩
  cases b
  · let Q : (Fin (j - (e : ℕ)) → Fin (2 * r + k + 1)) → Wsm (E := E) (Sd z z' j hj) := fun B =>
      (qminor (fun a b => EHt (E := E) (Sd z z' j hj) hU₀ a b) B (C3.sR k r (j - (e : ℕ)) hm)
        ((y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2 + ((j - (e : ℕ) : ℕ) : ℂ) - 1)) h
    let ψ : (Fin (j - (e : ℕ)) → Fin (2 * r + k + 1)) → Mat k r → ℂ := fun B g =>
      (Matrix.of fun a l : Fin (j - (e : ℕ)) =>
        ((Hpk k r * gᴴ * Hpk k r) *ᵥ bvec (eI k r (Fin.castLE hm a))) (B l)).det
    have hψ : ∀ B, ContDiff ℝ ⊤ (ψ B) := by
      intro B
      apply contDiff_det'
      intro a l
      simp only [Matrix.of_apply, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply]
      fun_prop
    let S : Mat k r → E := fun g => ∑ B : Fin (j - (e : ℕ)) → Fin (2 * r + k + 1),
      if StrictMono (fun l => C3.keyS k r (B l)) then ψ B g • (Q B).1 g else 0
    have hS : Loc (⊤ : ℕ∞) S g₀ := by
      apply loc_sum
      intro B _
      by_cases hB : StrictMono (fun l => C3.keyS k r (B l))
      · simp only [if_pos hB]
        exact loc_smulFun _ (hψ B) ((Q B).2 g₀ hg hgG)
      · simp only [if_neg hB]
        exact loc_zero' g₀
    have hT := loc_invsmul (fun g => starRingEnd ℂ (Dmin k r z z' g ⟨j, by omega⟩))
      ((contDiff_starC).comp (contDiff_Dmin z z' _)) ((map_ne_zero _).2 hg) hS
    refine loc_of_eq hT hU₀ hg (fun x hx hxG => ?_)
    show D.vLet k r z z' j hj (false, y) e h.1 x = _
    unfold D.vLet
    rw [if_neg h10, if_neg Bool.false_ne_true]
    congr 1
    unfold C3.AAvop
    apply Finset.sum_congr rfl
    intro B _
    by_cases hB : StrictMono (fun l => C3.keyS k r (B l))
    · rw [if_pos hB, if_pos hB, qminor_agree _ hU₀ _ _ _ h x hx hxG, inv_GV hxG]
    · rw [if_neg hB, if_neg hB]
  · let Q : (Fin (j - (e : ℕ)) → Fin (2 * r + k + 1)) → Wsm (E := E) (Sd z z' j hj) := fun c =>
      (qminor (fun a b => EHt (E := E) (Sd z z' j hj) hU₀ a b) (C3.xR k r (j - (e : ℕ)) hm) c
        ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2)) h
    let ψ : (Fin (j - (e : ℕ)) → Fin (2 * r + k + 1)) → Mat k r → ℂ := fun c g =>
      (Matrix.of fun a l : Fin (j - (e : ℕ)) =>
        herm (Hpk k r) (g *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))).det
    have hψ : ∀ c, ContDiff ℝ ⊤ (ψ c) := by
      intro c
      apply contDiff_det'
      intro a l
      simp only [Matrix.of_apply, herm, mulVec, dotProduct]
      fun_prop
    let S : Mat k r → E := fun g => ∑ c : Fin (j - (e : ℕ)) → Fin (2 * r + k + 1),
      if StrictMono c then ψ c g • (Q c).1 g else 0
    have hS : Loc (⊤ : ℕ∞) S g₀ := by
      apply loc_sum
      intro c _
      by_cases hc : StrictMono c
      · simp only [if_pos hc]
        exact loc_smulFun _ (hψ c) ((Q c).2 g₀ hg hgG)
      · simp only [if_neg hc]
        exact loc_zero' g₀
    have hg' : Dmin k r z z' g₀ ⟨j, by omega⟩ ≠ 0 := hg
    have hT := loc_invsmul (fun g => Dmin k r z z' g ⟨j, by omega⟩) (contDiff_Dmin z z' ⟨j, by omega⟩) hg' hS
    refine loc_of_eq hT hU₀ hg (fun x hx hxG => ?_)
    show D.vLet k r z z' j hj (true, y) e h.1 x = _
    unfold D.vLet
    rw [if_neg h10, if_pos rfl]
    congr 1
    unfold C3.AAop
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : StrictMono c
    · rw [if_pos hc, if_pos hc, qminor_agree _ hU₀ _ _ _ h x hx hxG]
    · rw [if_neg hc, if_neg hc]

theorem uwG_mem {F : B.Mat k r → E} (hF : B.CkOn ⊤ (B.GV k r) F) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      D.uwG k r z z' F j hj w e ∈ Wsm (E := E) (Sd z z' j hj)
  | [], _ => fun g _ hgG => hF g hgG
  | l :: w, e => vLet_mem z z' j hj l (e 0) ⟨_, uwG_mem hF w fun a => e a.succ⟩

theorem uwG_letter_poly {F : B.Mat k r → E} (hF : B.CkOn ⊤ (B.GV k r) F) (w : List C.Letter)
    (e' : Wd.Ix (Fin w.length)) (g₀ : B.Mat k r) (hg₀ : g₀ ∈ GV k r) (hD : Dmin k r z z' g₀ ⟨j, by omega⟩ ≠ 0)
    (b : Bool) (e : Fin 2) :
    ∃ c : Fin (j + 1) → E, c (Fin.last j) = (if e = 0 then D.uwG k r z z' F j hj w e' g₀ else 0) ∧
      ∀ Y : ℝ, D.vLet k r z z' j hj (b, Y) e (D.uwG k r z z' F j hj w e') g₀ =
        ∑ l : Fin (j + 1), ((Y : ℂ) ^ (l : ℕ)) • c l :=
  vLet_poly hj z z' _ g₀ hg₀ hD (uwG_mem z z' j hj hF w e' g₀ hD hg₀) b e

end smooth

end Formalism.FourierDecayAlt.P.PBG
