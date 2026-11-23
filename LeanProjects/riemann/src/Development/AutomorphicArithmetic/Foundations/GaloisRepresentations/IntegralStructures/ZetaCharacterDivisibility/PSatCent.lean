import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

open GlobalTheory.LFun Formalism.UG Matrix in

private theorem scalar_unit_mem {E : Type} [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (u : (w.adicCompletion E)ˣ) (hu : Valued.v (u : w.adicCompletion E) = 1) :
    GeneralLinearGroup.scalar (Fin a) u ∈ KGL w a := by
  have hv : Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have m1 : (u : w.adicCompletion E) ∈ Ov E w := le_of_eq hu
  have m2 : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ Ov E w := le_of_eq hv
  have hinj : Function.Injective fun M : Matrix (Fin a) (Fin a) (Ov E w) => M.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.scalar (Fin a) (⟨u, m1⟩ : Ov E w), Matrix.scalar (Fin a) (⟨_, m2⟩ : Ov E w), hinj ?_, hinj ?_⟩,
    Units.ext ?_⟩
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · ext i j
    by_cases h : i = j
    · subst h; simp [bc]
    · simp [bc, h]

open GlobalTheory.LFun Formalism.UG Matrix in

private theorem satEig_self (q n : ℕ) (B : Multiset ℂˣ) (hB : B.card = n) :
    satEig q n B n = ((B.prod : ℂˣ) : ℂ) := by
  subst hB
  have hc : (B.map fun b : ℂˣ => (b : ℂ)).card = B.card := Multiset.card_map _ _
  rw [satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
  conv_lhs => rw [← hc]
  rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
  exact (map_multiset_prod (Units.coeHom ℂ) B).symm

open GlobalTheory.LFun Formalism.UG Matrix in

private theorem scalar_unif_act {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V] {a : ℕ}
    {w : HeightOneSpectrum (𝓞 E)} {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {x : V}
    {B : Multiset ℂˣ} (hx : IsSatVecGL w ρ x B) (u : (w.adicCompletion E)ˣ)
    (hu : IsUnifV E w (u : w.adicCompletion E)) :
    ρ (GeneralLinearGroup.scalar (Fin a) u) x = ((B.prod : ℂˣ) : ℂ) • x := by
  have h0 : (u : w.adicCompletion E) ≠ 0 := u.ne_zero
  set z : GL (Fin a) (w.adicCompletion E) := GlobalTheory.WeylGL.tor h0 fun _ => 1 with hz
  have hzs : z = GeneralLinearGroup.scalar (Fin a) u := by
    ext i j
    simp [hz, GlobalTheory.WeylGL.tor_val, Matrix.diagonal_apply]
  have hcomm : ∀ g, z * g = g * z := GlobalTheory.WeylGL.tor_const_comm h0 1
  have hT : Tj ℂ a (Ov E w) (u : w.adicCompletion E) a = dosetInd ℂ (KGL w a) z := by
    rw [GlobalTheory.WeylGL.Tj_eq h0]; simp [hz]
  have h1 := hx.2.2.2 _ hu a le_rfl
  rw [hT, heckeVec_dosetInd (R := {z}) hx.2.1, Finset.sum_singleton, satEig_self _ _ _ hx.2.2.1, hzs] at h1
  · exact h1
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro g hg
    obtain ⟨c, hc, d, hd, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨z, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← hcomm c, mul_assoc, inv_mul_cancel_left]
    exact mul_mem hc hd

theorem UpperTheory.Gal.Int.Div.satCent_of :
    SatCent := by
  intro E _ _ a w σ B hB
  obtain ⟨x, hx⟩ := hB.exists_vec
  exact ⟨x, hx.1, fun u hu => GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ (scalar_unit_mem a w u hu),
    fun u hu => scalar_unif_act hx u hu⟩
