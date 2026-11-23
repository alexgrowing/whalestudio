import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharactersEightfoldProductEqEighthPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharacStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMapOfIntegralMatrixActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataEighthPowerViaCharacterMapsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E : EndU U.toUnifPre, (∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN hinj hfin D₀ e₀ hR G₀ _ _ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G _ _ hG D U q hq hqu hqc
  obtain ⟨ch, hch, hbij⟩ := GlobalTheory.T.characters_eightfold_product_eq_eighthPower V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq hqu
  let act : Matrix (Fin 8) (Fin 8) ℤ → (Fin 8 → Q.X) → (Fin 8 → Q.X) := fun N mu u => ∑ v, N u v • mu v
  have hact : ∀ N N' mu, act N (act N' mu) = act (N * N') mu := by
    intro N N' mu
    funext u
    simp only [act, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  have hone : ∀ mu, act 1 mu = mu := by
    intro mu
    funext u
    simp [act, Matrix.one_apply]
  have hdet : IsUnit (W + W.transpose).det := by rw [hW.2]; exact isUnit_one
  have hM1 : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hM2 : (W + W.transpose)⁻¹ * (W + W.transpose) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hactadd : ∀ N mu mu', act N (mu + mu') = act N mu + act N mu' := by
    intro N mu mu'
    funext u
    simp [act, smul_add, Finset.sum_add_distrib]
  let f : (Fin 8 → Q.X) →+ D.toPre.X :=
    { toFun := fun mu => ∑ u, ch u (e₀.symm (act (W + W.transpose) mu u))
      map_zero' := by
        have : act (W + W.transpose) 0 = 0 := by funext u; simp [act]
        simp [this]
      map_add' := by
        intro mu mu'
        simp only [hactadd, Pi.add_apply, map_add, Finset.sum_add_distrib] }
  have hfb : Function.Bijective f := by
    have hA : Function.Bijective (act (W + W.transpose)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨act (W + W.transpose)⁻¹ x, by rw [hact, hM1, hone]⟩⟩
      have := congrArg (act (W + W.transpose)⁻¹) hxy
      rwa [hact, hact, hM2, hone, hone] at this
    have hE : Function.Bijective (fun x : Fin 8 → Q.X => fun u => e₀.symm (x u)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨fun u => e₀ (x u), by funext u; simp⟩⟩
      funext u
      exact e₀.symm.injective (congrFun hxy u)
    exact hbij.comp (hE.comp hA)
  let e : (Fin 8 → Q.X) ≃+ D.toPre.X := AddEquiv.ofBijective f hfb
  refine ⟨e, GlobalTheory.T.degenerationData_eighthPower_via_characterMaps g n o ζ F W hW V Q V₁ ρ hCN hinj hfin D₀ e₀ hR G₀ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G hG D U q hq hqu hqc ch hch e (fun mu => rfl), ?_⟩
  intro a a' hM E hE mu
  have hEc := GlobalTheory.T.uniformisation_endomorphism_closedFibreTorus_characterMap V₁ hCN D P G hG U E
  have key := GlobalTheory.T.characterMap_of_integral_matrix_action V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq ch hch a E.aG E.h E.homG hEc hE
  show E.h (f mu) = f (act a' mu)
  simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [← map_zsmul, ← map_sum]
  congr 2
  have h3 : act (W + W.transpose) (act a' mu) = act a.transpose (act (W + W.transpose) mu) := by
    rw [hact, hact, hM]
  rw [h3]
  simp [act, Matrix.transpose_apply]
