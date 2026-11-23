import Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.SquareIntegrableOfLatticeTorus

noncomputable section

namespace PositivityTheory.ThKEst.Sq

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]⟩

theorem res_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {a b n : ℕ} (h₁ : ResEtaPow K χ₁ a) (h₂ : ResEtaPow K χ₂ b)
    (he : Even (a + b)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e : (-1 : ℂ) ^ a = (-1) ^ b := neg_one_pow_congr (Nat.even_add.1 he)
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x, hn.neg_one_pow, e, ite_self, div_self]
  split_ifs <;> simp

theorem triplePair_holds : TriplePair := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  have g := h.geo.eBig
  exact ⟨⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      res_div h.chars.resβ h.chars.resα h.geo.even h.geo.even, h.weil⟩,
    ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      res_div h.chars.resα h.chars.resβ (add_comm a a' ▸ h.geo.even) h.geo.even, h.weil'⟩, by omega⟩

theorem sqInt_of_leaves (hTh : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hA : SqAll) (hO : SqSo) (hF : SoFin)
    (hC : LatCpt) (hT : LatTor) (hL : LatFull) : SqInt :=
  sqInt_of triplePair_holds (square_integrable_of_lattice_torus hG hE hS hTh hA hF hC hT) (square_integrable_orthogonal_case hG hE hS hTh hO hF hC hL)

end PositivityTheory.ThKEst.Sq
