import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def BorDesc : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
    ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R) (yq : FrPt Xo c q.R),
      FrMap φ yp y → FrMap ψ yq y' →
      ∃ (r : TRing c.F) (α : p.R →ₐ[c.F] r.R) (β : q.R →ₐ[c.F] r.R) (χ : r.R →ₐ[c.F] S)
        (z z' : FrPt Xo c r.R) (t₀ : Ix Dw → (r.R)ˣ),
        χ.comp α = φ ∧ χ.comp β = ψ ∧ FrMap α yp z ∧ FrMap β yq z' ∧ FrBor t₀ z z' ∧
          ∀ i, χ (t₀ i : r.R) = (t i : S)

def IntLatU : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io), letI := io.toAlgebra; y'.1.x = y.1.x →
    (∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧
      ∀ i, IsCombAt y.1.x (y.1.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.1.u τ i)) ∧
    ∀ (a : T.Frˣ) (pm : Gx y'.1.x ⟶ Gx y.1.x),
      pm ≫ (CartesianMonoidalCategory.snd (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.snd (Over.mk y'.1.x) Xo.univ.t.G).left →
      pm ≫ (CartesianMonoidalCategory.fst (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.fst (Over.mk y'.1.x) Xo.univ.t.G).left →
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.1.x).U i ≤ pm ⁻¹ᵁ (PPx y.1.x).U i),
        (pm.appLE _ _ h).hom (scal y.1.x (a : T.Fr) i * y.1.s.f i) = y'.1.s.f i) →
      valV T.V (a : T.Fr) = 1

end Open

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem wtField_of (hD : BorDesc Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  have key : ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R)
      (yq : FrPt Xo c q.R), FrMap φ yp y → FrMap ψ yq y' → ψ (f q yq) = wchar (ex Dw a n) t * φ (f p yp) := by
    intro p q φ ψ yp yq hp hq
    obtain ⟨r, α, β, χ, z, z', t₀, hα, hβ, hz, hz', hb₀, ht⟩ := hD S t y y' hb p q φ ψ yp yq hp hq
    rw [← hα, ← hβ, AlgHom.comp_apply, AlgHom.comp_apply, ← hf.1 p r α yp z hz, ← hf.1 q r β yq z' hz',
      hf.2 r t₀ z z' hb₀, map_mul]
    congr 1
    simp only [wchar, map_prod, map_pow, ht]
  unfold evR evalAt
  rw [dif_pos hy, dif_pos hy']
  exact key _ _ _ _ _ _ hy.choose_spec.choose_spec.choose_spec hy'.choose_spec.choose_spec.choose_spec

theorem valV_algebraMap_unit (T : CDVR) {u : T.V} (hu : IsUnit u) :
    valV T.V (algebraMap T.V T.Fr u) = 1 := by
  unfold valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro h
  exact (IsDiscreteValuationRing.maximalIdeal T.V).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem intDiagUnit_of (hL : IntLatU Xo c) : IntDiagUnit Xo c := by
  intro T io y y' t hb k
  let := io.toAlgebra
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hb
  obtain ⟨hA, hG⟩ := (show IntLatU Xo c from hL) T io y y' hx
  rcases k with _ | ⟨τ, i⟩
  · exact hG (t none) pm h1 h2 h3
  obtain ⟨A, hdet, hAc⟩ := hA τ

  have hrow : ∀ i', ∃ cf : Fin (Dw.mult τ) → T.Fr, cf i' = (t (some ⟨τ, i'⟩) : T.Fr) ∧
      (∀ j, i' < j → cf j = 0) ∧ ∀ j, algebraMap T.V T.Fr (A i' j) = cf j := by
    intro i'
    obtain ⟨cf, hci, hcz, hcomb⟩ := hu τ i'
    have htan : IsTanAt y.1.x (y'.1.u τ i') := hx ▸ y'.1.tan τ i'
    obtain ⟨a0, -, huniq⟩ := y.1.basis τ (y'.1.u τ i') htan (y'.1.eig τ i')
    have e1 := huniq cf hcomb
    have e2 := huniq _ (hAc i')
    exact ⟨cf, hci, hcz, fun j => congrFun (e2.trans e1.symm) j⟩
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hlow : A.IsLowerTriangular := by
    intro i' j hij
    obtain ⟨cf, -, hcz, hA'⟩ := hrow i'
    apply hinj
    rw [hA' j, hcz j hij, map_zero]
  rw [Matrix.det_of_isLowerTriangular A hlow, IsUnit.prod_univ_iff] at hdet
  obtain ⟨cf, hci, -, hA'⟩ := hrow i
  rw [← hci, ← hA' i]
  exact valV_algebraMap_unit T (hdet i)

end Proofs

end Formalism.L2.Pj
