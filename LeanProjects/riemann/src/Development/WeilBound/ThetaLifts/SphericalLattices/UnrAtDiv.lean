import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
import Development.WeilBound.ThetaLifts.DoubleEigenvalues.DblEigenW

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem inert_ctx {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {v : Pl F} (he : IsEmpty (E →ₐ[F] Fv F v)) :
    (∃ w, Formalism.UG.IsInertAt F E v w) ∧ v ∉ X.T :=
  ⟨inert_of_local F E σ B hT.base v he, fun hv => he.false (B.τ ⟨v, hT.chars.sub hv⟩)⟩

theorem unrAt_div {χ χ' : Chr F E} {u : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ u) (h' : UnrAt χ' u) :
    UnrAt (χ / χ') u := fun x hx => by
  have e : χ / χ' * χ' = χ := div_mul_cancel χ χ'
  have e2 : locChar (χ / χ' * χ') u x = locChar (χ / χ') u x * locChar χ' u x := by simp [locChar]
  rw [e, h x hx, h' x hx, mul_one] at e2
  exact e2.symm

theorem fix_of {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} (hM : M.IsGood B.ψ) {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil B.ψ χX χW om) {v : Pl F} (hX' : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt χX u)
    (hW' : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt χW u)
    {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}
    (hL : IsLocRep M B.ψ om v ω ρ) :
    (∀ g ∈ KAt σ X v, ω (g, 1) (M.vac v) = M.vac v) ∧ (∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) := by
  have hSB := (hM.vac v).1
  refine ⟨fun g hg => ?_, fun k hk => ?_⟩
  · have hA := PositivityTheory.ThKU.Vac.vacFixX hB hX hW hM hw hW' (k := g) hg
    exact ((hL.acts g hg.1 1 (GlobalTheory.InertSph.one_mem_KAt σ W v).1 _ hSB _).1 hA).symm
  · have hA := PositivityTheory.ThKU.Vac.vacFixW hB hX hW hM hw hX' (k := k) hk
    exact ((hL.acts 1 (GlobalTheory.InertSph.one_mem_KAt σ X v).1 k hk.1 _ hSB _).1 hA).symm

end PositivityTheory.Sph

end
