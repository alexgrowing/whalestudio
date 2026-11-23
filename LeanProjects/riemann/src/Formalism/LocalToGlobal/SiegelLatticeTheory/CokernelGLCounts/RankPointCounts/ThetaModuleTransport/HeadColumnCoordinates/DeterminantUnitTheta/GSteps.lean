import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.TraceUniformizerEqNegOne

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Cut

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def ZZm (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  HermSp.ZZplusOf M Zh T T' + Matrix.of fun a b => cor r a b (g.e.symm (-T / (g.q : F), T' / (g.q : F)))

def laG (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (l : Fin (r + 1) → M.R) : E :=
  (Zm⁻¹.mulVec fun i => (l i : E)) (Fin.last r)

abbrev mk1 (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (l : Fin (r + 1) → M.R) : DD1 hs Z TT :=
  QuotientAddGroup.mk l

def Gam1 (hs : M.split = some g) (Z : M.Mat (r + 1)) (TT : M.R) (Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Set (DD1 hs Z TT × DD1 hs Z TT × M.R × E) :=
  {p | ∃ (l : Fin (r + 1) → M.R) (η : M.R),
    p = (mk1 hs Z TT (η • eV r + q2 hs • l), mk1 hs Z TT l, η, laG Zm l)}

variable {Z₁ Z₂ : M.Mat (r + 1)} {TT : M.R}

def OLin (hs : M.split = some g) (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) : Prop :=
  ∀ (c : 𝒪[F]) (l l₂ : Fin (r + 1) → M.R), θ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
    θ (mk1 hs Z₁ TT (dgR hs c • l)) = mk1 hs Z₂ TT (dgR hs c • l₂)

def Match1 (hs : M.split = some g) (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (Zm₁ Zm₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  (fun p => (θ p.1, θ p.2.1, p.2.2.1, p.2.2.2)) '' Gam1 hs Z₁ TT Zm₁ = Gam1 hs Z₂ TT Zm₂

def Ind (hs : M.split = some g) (γ : IsoMbe Z₁.Z Z₂.Z) (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) : Prop :=
  ∀ l l₂ : Fin (r + 1) → M.R, γ.1 (Submodule.Quotient.mk l) = Submodule.Quotient.mk l₂ →
    θ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂

private theorem split_symm_pair_zero_mem_O (c : F) (hc : c ∈ 𝒪[F]) : g.e.symm (c, 0) ∈ M.L.O := by
  rw [M.L.O_def]
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C ⟨c, hc⟩),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C _), ?_⟩
  have hmap : algebraMap (𝒪[F]) E ⟨c, hc⟩ = algebraMap F E c := rfl
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_sub, Polynomial.eval₂_C, hmap]
  apply g.e.injective
  simp [map_mul, map_sub, AlgEquiv.commutes, Prod.algebraMap_apply]

private theorem split_coords_mem_integers_of_mem_R (hs : M.split = some g) (y : E) (hy : y ∈ M.R) :
    (g.e y).1 ∈ 𝒪[F] ∧ ((g.e y).2 - (g.e y).1) / (g.q : F) ∈ 𝒪[F] := by
  unfold Model.R at hy
  rw [hs] at hy
  simp only [Subring.mem_comap, Subring.mem_map, RingHom.mem_eqLocus] at hy
  obtain ⟨⟨a, b⟩, hab, he⟩ := hy
  have he' : g.e y = ((a : F), (b : F)) := he.symm
  rw [he']
  refine ⟨a.2, ?_⟩
  simp only [RingHom.comp_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hab
  obtain ⟨d, hd⟩ := hab
  change d * g.q = a - b at hd
  have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have hd' : (d : F) * (g.q : F) = (a : F) - (b : F) := by
    have := congrArg Subtype.val hd
    push_cast at this
    exact this
  have key : ((b : F) - (a : F)) / (g.q : F) = ((-d : 𝒪[F]) : F) := by
    rw [div_eq_iff hq]
    push_cast
    linear_combination hd'
  rw [key]
  exact (-d).2

theorem iotaOne_mem_first (hs : M.split = some g) (x : M.R) : g.e.symm ((g.e (x : E)).1, 0) ∈ M.L.O := split_symm_pair_zero_mem_O _ (split_coords_mem_integers_of_mem_R hs _ x.2).1

theorem iotaOne_mem_second (hs : M.split = some g) (x : M.R) :
    g.e.symm (((g.e (x : E)).2 - (g.e (x : E)).1) / (g.q : F), 0) ∈ M.L.O := split_symm_pair_zero_mem_O _ (split_coords_mem_integers_of_mem_R hs _ x.2).2

def iota1 (hs : M.split = some g) (l : Fin (r + 1) → M.R) : Ix r → M.L.O
  | Sum.inl a => ⟨_, iotaOne_mem_first hs (l a)⟩
  | Sum.inr a => ⟨_, iotaOne_mem_second hs (l a)⟩

def iota2 (hs : M.split = some g) (l : Fin (r + 1) → M.R) : Ix r → M.L.O :=
  fun i => ⟨M.L.cj (iota1 hs l i), cj_mem_O M.L (iota1 hs l i).2⟩

variable {Zσ₁ Zσ₂ : M.Mat (r + 1)}

def IsoB (hs : M.split = some g) (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT)
    (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) : Prop :=
  ∀ l l₂ w w₂ : Fin (r + 1) → M.R, θ₁ (mk1 hs Z₁ TT l) = mk1 hs Z₂ TT l₂ →
    θ₂ (mk1 hs Zσ₁ TT w) = mk1 hs Zσ₂ TT w₂ →
    formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₂ (algebraMap F E T) (algebraMap F E T')
        (iota1 hs l₂) (iota2 hs w₂) -
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh₁ (algebraMap F E T) (algebraMap F E T')
        (iota1 hs l) (iota2 hs w) ∈ M.L.O

end Cut

section Steps

def GHyp {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) {r : ℕ} (T T' : F) (TT : M.R)
    (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z Zσ : M.Mat (r + 1)) : Prop :=
  (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) ∧ (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) ∧
    g.e (TT : E) = (T, T') ∧ Z.Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' ∧
    Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T' ∧ IsUnit Zh.det ∧
    IsUnit (Zh.det * M.L.cj Zh.det - algebraMap F E (T * T') *
      ((Zh.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh.submatrix Fin.castSucc Fin.castSucc).det))

def KapEq {E : Type} [CommRing E] {r : ℕ} (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det = Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det

def StepSplit : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card {p : (DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) × (DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT) //
        OLin hs p.1 ∧ OLin hs p.2 ∧ Match1 hs p.1 (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') ∧
        Match1 hs p.2 (ZZm g (Zh₁.map M.L.cj) T T') (ZZm g (Zh₂.map M.L.cj) T T') ∧
        IsoB hs Zh₁ Zh₂ T T' p.1 p.2}

def FirstIsometryForward : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT, OLin hs θ → Match1 hs θ (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') →
      ∃ γ : IsoMbe Z₁.Z Z₂.Z, Ind hs γ θ

def FirstIsometryBackward : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT,
      OLin hs θ ∧ Match1 hs θ (ZZm g Zh₁ T T') (ZZm g Zh₂ T T') ∧ Ind hs γ θ

def FirstIsometryUniqueness : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ (θ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (γ γ' : IsoMbe Z₁.Z Z₂.Z), Ind hs γ θ → Ind hs γ' θ → γ = γ'

def StepDu : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ γ : IsoMbe Z₁.Z Z₂.Z, ∃ γ' : IsoMbe Zσ₁.Z Zσ₂.Z,
      ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT),
        Ind hs γ θ₁ → Ind hs γ' θ₂ → IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂

def StepDuU : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F) (TT : M.R)
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ Zσ₁ Zσ₂ : M.Mat (r + 1)),
    GHyp M g T T' TT Zh₁ Z₁ Zσ₁ → GHyp M g T T' TT Zh₂ Z₂ Zσ₂ → KapEq Zh₁ Zh₂ →
    ∀ (θ₁ : DD1 hs Z₁ TT ≃+ DD1 hs Z₂ TT) (θ₂ θ₂' : DD1 hs Zσ₁ TT ≃+ DD1 hs Zσ₂ TT),
      IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂ → IsoB hs Zh₁ Zh₂ T T' θ₁ θ₂' → θ₂ = θ₂'

def StepZsig : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g → ∀ (r : ℕ) (T T' : F),
    (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) → (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
    ∀ (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
      Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T' → IsUnit Zh.det →
      (∃ TT : M.R, g.e (TT : E) = (T, T')) ∧ IsUnit (Z.map M.R.subtype).det ∧
      ∃ Zσ : M.Mat (r + 1), Zσ.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh.map M.L.cj) T T'

end Steps

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
