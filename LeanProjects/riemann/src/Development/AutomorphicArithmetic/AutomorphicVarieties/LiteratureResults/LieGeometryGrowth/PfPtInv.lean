import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfInvLie
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem open_stab {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

theorem UpperTheory.V.Lit.Geo.Pf.ptInv :
    UpperTheory.V.Lit.Geo.Pf.PtInv := by
  intro E _ _ _ a χ d G x y
  have h : ∀ g, Pf.pt χ G x y g = ∑ i, ∑ j, G i j *
      (starRingEnd ℂ ((mulChi a χ (cmp i x)).1 g) * (mulChi a χ (cmp j y)).1 g) := by
    intro g
    have hn : ((‖((chiDet a χ g : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        starRingEnd ℂ ((chiDet a χ g : ℂˣ) : ℂ) * ((chiDet a χ g : ℂˣ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; rfl
    simp only [Pf.pt, hn, mulChi_apply, Pf.cmp_ev, dotProduct, Matrix.mulVec, Finset.mul_sum, map_mul, Pi.star_apply,
      Complex.star_def]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hc : Pf.TwInv χ x → Pf.TwInv χ y → Pf.CInv (Pf.pt χ G x y) := by
    intro hx hy
    rw [show Pf.pt χ G x y = _ from funext h]
    refine Pf.CInv.sum _ fun i => Pf.CInv.sum _ fun j => ⟨?_, fun γ g => ?_, fun t g => ?_⟩
    · exact continuous_const.mul ((Complex.continuous_conj.comp (Pf.invLie E a _ (hx i)).1.cont).mul
        (Pf.invLie E a _ (hy j)).1.cont)
    · rw [(hx i).left, (hy j).left]
    · rw [(hx i).centre, (hy j).centre]
  refine ⟨h, hc, fun θ hθ hx hy => ⟨fun γ g => ?_, fun t g => ?_, ?_⟩⟩
  · rw [hθ, hθ, (hc hx hy).left]
  · rw [hθ, hθ, (hc hx hy).centre]
  · change IsOpen {k | finRep E a k θ = θ}
    have ox : IsOpen (⋂ i, {k | finRep E a k (mulChi a χ (cmp i x)) = mulChi a χ (cmp i x)}) :=
      isOpen_iInter_of_finite fun i => (hx i).level
    have oy : IsOpen (⋂ i, {k | finRep E a k (mulChi a χ (cmp i y)) = mulChi a χ (cmp i y)}) :=
      isOpen_iInter_of_finite fun i => (hy i).level
    refine open_stab (finRep E a) θ (ox.inter oy) ⟨by simp, by simp⟩ ?_
    rintro k ⟨h1, h2⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at h1 h2
    have e : ∀ φ : Sm E a, finRep E a k φ = φ → ∀ g, φ.1 (g * finGL E a k) = φ.1 g := fun φ hφ g =>
      congrFun (congrArg Subtype.val hφ) g
    refine Subtype.ext (funext fun g => ?_)
    change θ.1 (g * finGL E a k) = θ.1 g
    rw [hθ, hθ, h, h]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [e _ (h1 i), e _ (h2 j)]
