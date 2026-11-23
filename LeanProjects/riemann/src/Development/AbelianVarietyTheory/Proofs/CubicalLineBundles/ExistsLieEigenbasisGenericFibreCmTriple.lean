import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueExtendRingOfIntegersHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignatureStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsLocalModelOfIntegral

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_eigenbasis_fibre : Out.SecTwistSt → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))) (oa : T.pol.OAct (𝓞 E)) (S : Set (E →+* ℂ)) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), oa.act = T.t.act.act → Function.Bijective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → HasType H T.t.act ρ 1 0 → ∃ (x : KeyIn K) (φ : x.P.A.left ⟶ T.pol.A.left) (τ : Fin x.P.g ≃ S), IsFibreOf T.pol x (gmap K) φ ∧ x.P.g = Module.finrank ℚ E / 2 ∧ IsLieType T.pol oa x φ τ lab := by
  intro hT hL E _ _ _ _ H K _ _ T oa S lab ρ hoa hlab hρ hS hty
  classical
  obtain ⟨-, -, h3⟩ := GlobalTheory.CM.splits_basic E
  obtain ⟨hs1, hs2, -⟩ := h3 K
  have hsp : Splits E K := hs1.2 (by
    rw [← Nat.card_eq_of_bijective lab hlab, Nat.card_eq_fintype_card, NumberField.Embeddings.card])
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  obtain ⟨F₀⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange hL.polBaseChange K T.pol
  have hg : T.g = Module.finrank ℚ E / 2 := by
    simpa using (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ T F₀ 1 0 hsp hty hρ).2.2.2.1
  obtain ⟨y, ψ, w, hyg, hψ, hw⟩ := GlobalTheory.KeyPow.exists_keyIn_pullback hT (algebraMap (𝓞 K) K) T.pol (hpos.trans_eq hg.symm)
  have hfib : IsFibreOf T.pol y (spMap (algebraMap (𝓞 K) K)) ψ := ⟨hψ, w, (isGen_iff _).2 hw⟩
  let F : GenFib T.pol := ⟨y.P, ψ, (isFibreOf_iff_isPolFibre _ _ _ _ _ _).1 hfib, y.v, y.basis⟩
  obtain ⟨hrk, hind, -, -, hcard, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ T F 1 0 hsp hty hρ
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K T.pol F (𝓞 E) T.t.act
  let res : S → (𝓞 E →+* 𝓞 K) := fun t => RingOfIntegers.mapRingHom (lab t)
  have hres : ∀ t (a : 𝓞 E), ((res t a : 𝓞 K) : K) = lab t (a : E) := fun t a => rfl
  have hinj : Function.Injective res := fun s t h => Subtype.ext (hlab.1
    ((hs2 (res t)).unique (fun a => by rw [← h, hres]) (fun a => by rw [hres])))
  have hrt : ∀ t, res t H.rt = ρ := fun t => RingOfIntegers.ext ((hres t _).trans ((hS t).1 t.2))
  have hcS : Nat.card S = Module.finrank ℚ E / 2 := by
    rw [← hcard]
    refine Nat.card_eq_of_bijective (fun t => ⟨res t, hrt t⟩) ⟨fun s t h => hinj (congrArg Subtype.val h), fun τ => ?_⟩
    obtain ⟨τ', hτ', -⟩ := hs2 τ.1
    obtain ⟨t, rfl⟩ := hlab.2 τ'
    refine ⟨⟨t, (hS t).2 (by rw [hτ', τ.2])⟩, Subtype.ext (RingHom.ext fun a => RingOfIntegers.ext ?_)⟩
    exact (hres _ _).trans (hτ' a)
  have hb : ∀ t : S, ∃ b ∈ Submodule.span K (F.eigLat T.t.act (res t) : Set (Fin F.P₀.g → K)), b ≠ 0 := fun t => by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    have := hrk (res t)
    rw [latRank, h, if_pos (hrt t), finrank_bot] at this
    exact zero_ne_one this
  choose b hb hb0 using hb
  have hli : LinearIndependent K b := (hind.comp hinj).linearIndependent _ hb hb0
  have hyg' : y.P.g = Module.finrank ℚ E / 2 := hyg.trans hg
  let e : Fin y.P.g ≃ S := (Finite.equivFinOfCardEq (hcS.trans hyg'.symm)).symm
  let M : Matrix (Fin y.P.g) (Fin y.P.g) K := fun i => b (e i)
  have hM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 (hli.comp e e.injective))
  have := y.P.isAb.comm
  obtain ⟨hex, htan, hcomp, -, hbas⟩ := LieComb.lieComb_algebra K y.P.A _ y.v y.basis.1
  choose v' hv' _ using fun i => hex (M i)
  have hv'b : IsLieBasis v' := (hbas M v' y.basis hv').2 hM
  refine ⟨⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'b⟩, ψ, e, hfib, hyg', fun a i => ?_⟩
  obtain ⟨-, f₀, -, hf₀, hd⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K T.pol F T.pol F (T.t.act.act a) (T.t.act.hom a)
  have h1 : IsLieComb (r a (M i)) y.v (v' i ≫ f₀) := hd _ (hr a) _ _ (hv' i)
  obtain ⟨w', hw', -⟩ := (LieComb.lieComb_algebra K y.P.A _ v' hv'b.1).1 (Pi.single i (lab (e i) (a : E)))
  have h2 := hcomp _ M v' _ w' hv' hw'
  have h3 : r a (M i) = ∑ j, (Pi.single i (lab (e i) (a : E)) : Fin y.P.g → K) j • M j := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp), Pi.single_eq_same]
    exact ((hr' (res (e i)) _).2.1 (hb (e i)) a).trans rfl
  rw [h3] at h1
  refine ⟨w', hw', ?_⟩
  rw [← (hex _).unique h1 h2, hoa]
  exact (congrArg ((v' i).left ≫ ·) hf₀.symm).trans (Category.assoc _ _ _).symm

end GlobalTheory.LamF
