import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem gen_of {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
    {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}
    (hL : IsLocRep M ψ om v ω ρ) (hD : LocData M om v) :
    (∀ φ ∈ SB _, (∀ g ∈ KAt σ X v, ω (g, 1) φ = φ) →
      φ ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)}) ∧
    (∀ φ ∈ SB _, (∀ k ∈ KAt σ W v, ω (1, k) φ = φ) →
      φ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)}) := by
  obtain ⟨L, _, _, _, _, ϖ, σL, q, δ, JS, JT, ψL, ρL, ωL, ιS, ιT, s, hP, hs0, hsv, hspan, hsvac,
    hιS, hιT, hKS, hKT, hLoc⟩ := hD
  obtain ⟨h1, h2⟩ := GlobalTheory.Hk3.howeUnram_holds _ _ _ _ _ _ _ _ _ _ _ _ _ hP s hs0 hsv hspan
  have key : ∀ g h m, (↑(ωL (g, h) m) : Fn F n d v) = ω (ιS g, ιT h) ↑m := by
    intro g h m
    have hφ₁ := hL.pres _ (hιS g) _ (hιT h) _ m.2
    exact (hLoc g h m _ hφ₁).1 ((hL.acts _ (hιS g) _ (hιT h) _ m.2 _).2 rfl)
  have hS1 : ιS 1 = 1 := map_one ιS
  have hT1 : ιT 1 = 1 := map_one ιT
  constructor
  · intro φ hφ hfix
    have hw := h1 ⟨φ, hφ⟩ fun g hg => by
      apply Subtype.ext
      rw [key, hT1]
      exact hfix _ (by rw [kAt_eq]; exact hKS g hg)
    have hmap := Submodule.mem_map_of_mem (f := Submodule.subtype _) hw
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨ιT h, hιT h, by rw [Submodule.subtype_apply, key, hS1, hsvac]⟩
  · intro φ hφ hfix
    have hw := h2 ⟨φ, hφ⟩ fun h hh => by
      apply Subtype.ext
      rw [key, hS1]
      exact hfix _ (by rw [kAt_eq]; exact hKT h hh)
    have hmap := Submodule.mem_map_of_mem (f := Submodule.subtype _) hw
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨ιS g, hιS g, by rw [Submodule.subtype_apply, key, hT1, hsvac]⟩

end PositivityTheory.Sph

end
