import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetLeftMem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermFrobeniusTorsionJetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf.PeOne

theorem homAt_comp' {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A] [Algebra S A]
    [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 (g.comp f) = homAt x0 g ≫ homAt x0 f := by
  ext1
  simp only [homAt, spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem jetSubstP_mk_X {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (i : κ) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]

theorem jetCopy_mkX {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (i : Fin n) (j : Fin d) :
    jetCopy (S := S) d m i (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
  rw [MvPolynomial.aeval_X]

theorem constantCoeff_psIn {S : Type} [CommRing S] {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n')
    (f : MvPowerSeries (Fin n × Fin d) S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.constantCoeff (psIn d m r f) = 0 := by
  unfold psIn
  rw [MvPolynomial.constantCoeff_rename, psTrunc, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [MvPolynomial.constantCoeff_monomial]
  split_ifs with h
  · subst h
    simpa using hf
  · rfl

end GlobalTheory.CompanionTheory.Ar.Coc.Pf.PeOne

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

open PeOne in

theorem peG_act_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val (peG t x d g.x g.e (p + m + 1) ![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (homAt x (jq w p m)).left z J = 1 := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ x d g w m hp z J hJ
  have hring : (jq w p m).comp (jetSubstP (p + m + 1) fun q : Fin 2 × Fin d =>
      (![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j),
        fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) k) q.1 q.2) =
      ((jq w p m).comp (jetCopy d (p + m + 1) (1 : Fin 2))).comp (jetSubstP (p + m + 1) fun q : Fin 2 × Fin d =>
        (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k)
          q.1 q.2) := by
    refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun q => ?_)
    obtain ⟨a, j⟩ := q
    show _ = _
    simp only [AlgHom.comp_apply]
    refine Eq.trans (congrArg (jq w p m) (jetSubstP_mk_X _ _ _)) ?_
    refine Eq.trans ?_ (congrArg (fun u => jq w p m (jetCopy d (p + m + 1) (1 : Fin 2) u)) (jetSubstP_mk_X _ _ _)).symm
    fin_cases a
    · have h0 := GlobalTheory.T.germ_frobenius_torsion_jet E H hstar X0 t k p x d g w m hp j
      have hc := constantCoeff_psIn (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j) (g.B.A.const _ _)
      simp [hc, h0]
    · simp [jetCopy_mkX]
  have hcomp := congrArg (fun f => (homAt x f).left) hring
  simp only [homAt_comp', Over.comp_left] at hcomp
  refine (val_pull hJ _ _ _).trans ?_
  rw [hcomp]
  refine (val_pull hJ _ _ _).symm.trans ?_
  exact (val_corr hJ (g.axes _).1 _).trans (val_one _)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
