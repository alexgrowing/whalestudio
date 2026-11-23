import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ComponentsOfSecondComponentEq

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def asm (hs : M.split = some g) {T T' : F} {TT : M.R} {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    {Z Zσ : M.Mat (r + 1)} (h : GHyp M g T T' TT Zh Z Zσ)
    (ab : (DD1 hs Z TT × DD1 hs Z TT × M.R × E) × (DD1 hs Zσ TT × DD1 hs Zσ TT × M.R × E)) :
    DG g Zh T T' × DG g Zh T T' × (E × E) × (E × E) :=
  ((splitH hs h).symm (ab.1.1, ab.2.1), (splitH hs h).symm (ab.1.2.1, ab.2.2.1),
    pdat g (Zh⁻¹ (Fin.last r) (Fin.last r)) ab.1.2.2.1 ab.1.2.2.2 ab.2.2.2.1 ab.2.2.2.2)

abbrev GR (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :=
  GamRC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹)) Zh
    (algebraMap F E T) (algebraMap F E T')

def GamSubP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)) (h : GHyp M g T T' TT Zh Z Zσ),
    GR g Zh T T' ⊆ asm hs h '' (Gam1 hs Z TT (ZZm g Zh T T') ×ˢ Gam1 hs Zσ TT (ZZm g (Zh.map M.L.cj) T T'))

def GamSupP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)) (h : GHyp M g T T' TT Zh Z Zσ),
    asm hs h '' (Gam1 hs Z TT (ZZm g Zh T T') ×ˢ Gam1 hs Zσ TT (ZZm g (Zh.map M.L.cj) T T')) ⊆ GR g Zh T T'

variable (hs : M.split = some g) {T T' : F} {TT : M.R}

theorem R_ext {x y : M.R} (h1 : p1 g x = p1 g y) (h2 : p2 g x = p2 g y) : x = y := Subtype.ext (g.e.injective (Prod.ext h1 h2))

theorem E_ext {x y : E} (h1 : p1 g x = p1 g y) (h2 : p2 g x = p2 g y) : x = y := g.e.injective (Prod.ext h1 h2)

theorem pdat_inj {k : E} {η₁ η₂ η₁' η₂' : M.R} {a₁ a₂ a₁' a₂' : E}
    (h : pdat g k η₁ a₁ η₁' a₁' = pdat g k η₂ a₂ η₂' a₂') : η₁ = η₂ ∧ a₁ = a₂ ∧ η₁' = η₂' ∧ a₁' = a₂' := by
  unfold pdat at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have e1 := congrArg g.e h1
  have e2 := congrArg g.e h2
  have e3 := congrArg g.e h3
  have e4 := congrArg g.e h4
  simp only [AlgEquiv.apply_symm_apply, Prod.mk.injEq] at e1 e2 e3 e4
  obtain ⟨a1, a2⟩ := e1
  obtain ⟨b1, b2⟩ := e2
  obtain ⟨c1, c2⟩ := e3
  obtain ⟨d1, d2⟩ := e4
  have hη : η₁ = η₂ := R_ext a1 d1
  have hη' : η₁' = η₂' := R_ext a2 d2
  subst hη hη'
  exact ⟨rfl, E_ext (sub_right_inj.mp c1) (sub_right_inj.mp b1), rfl,
    E_ext (sub_right_inj.mp c2) (sub_right_inj.mp b2)⟩

theorem asm_inj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z Zσ : M.Mat (r + 1)} (h : GHyp M g T T' TT Zh Z Zσ) :
    Function.Injective (asm hs h) := by
  rintro ⟨⟨x1, x2, x3, x4⟩, ⟨y1, y2, y3, y4⟩⟩ ⟨⟨x1', x2', x3', x4'⟩, ⟨y1', y2', y3', y4'⟩⟩ hab
  unfold asm at hab
  simp only [Prod.mk.injEq] at hab
  obtain ⟨h1, h2, h3⟩ := hab
  have e1 := (splitH hs h).symm.injective h1
  have e2 := (splitH hs h).symm.injective h2
  simp only [Prod.mk.injEq] at e1 e2
  obtain ⟨q1, q2, q3, q4⟩ := pdat_inj h3
  obtain ⟨e11, e12⟩ := e1
  obtain ⟨e21, e22⟩ := e2
  subst_vars
  rfl

def mapD {A B : Type} (θ : A → B) (p : A × A × M.R × E) : B × B × M.R × E := (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)

theorem asm_compat {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)}
    (h₁ : GHyp M g T T' TT Zh₁ Z₁ Zσ₁) (h₂ : GHyp M g T T' TT Zh₂ Z₂ Zσ₂) (hk : KapEq Zh₁ Zh₂)
    (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT)
    (ab : (DD1 hs Z₁ TT × DD1 hs Z₁ TT × M.R × E) × (DD1 hs Zσ₁ TT × DD1 hs Zσ₁ TT × M.R × E)) :
    (fun p => (thetaOf hs h₁ h₂ θ₁ θ₂ p.1, thetaOf hs h₁ h₂ θ₁ θ₂ p.2.1, p.2.2.1, p.2.2.2)) (asm hs h₁ ab) =
      asm hs h₂ (Prod.map (mapD (M := M) θ₁) (mapD (M := M) θ₂) ab) := by
  have hk' := kap_common hk h₁.2.2.2.2.2.1 h₂.2.2.2.2.2.1
  simp only [asm, thetaOf, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, Prod.map, mapD, hk']
  rfl

end Formalism.L2.SG.LocalCountModules.AlgGSplit
