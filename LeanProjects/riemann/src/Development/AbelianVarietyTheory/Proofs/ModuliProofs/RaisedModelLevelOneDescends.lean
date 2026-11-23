import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.RaisedDescends

theorem map_nsmul_eq_pow {A Q : Type*} [AddMonoid A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c)
    (m : ℕ) (a : A) : f (m • a) = f a ^ m := by
  induction m with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact left_eq_mul.mp h
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem mono_spMap_of_isDedFrac {O F : Type} [CommRing O] [Field F] {β : O →+* F} (h : IsDedFrac β) :
    Mono (spMap β) := by
  letI := β.toAlgebra
  have := h.2.2
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F)
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isDedFrac_of_isInc (l : Level H) (S A : ℕ) (hS : 0 < S) (hA : l.A = A) (h1 : A = 1) (β : RZ H S A →+* KA l)
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) : IsDedFrac β := by
  subst hA
  exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l S 0 hS (by rw [h1, pow_zero])).2.2 β hβ

theorem Cpt_j_over {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F}
    (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem levComp_comp {D : Datum H} {l l' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o'' : Obj D l' b'' s''} {o' : Obj D l' b' s'} {o : Obj D l b s} {r : S' ⟶ S} {g : S'' ⟶ S'}
    (m : ObjMap o'' o' g) {ν : SABMap o'.t o.t r} (h : LevComp o' o r ν) (ν' : SABMap o''.t o.t (g ≫ r))
    (e : ν'.φ = m.toSABMap.φ ≫ ν.φ) : LevComp o'' o (g ≫ r) ν' := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := h.1 a
    rw [← map_nsmul_eq_pow _ o'.eta_add] at h1
    rw [← map_nsmul_eq_pow _ o''.eta_add, e, ← Category.assoc, m.eta, Category.assoc, h1, Category.assoc]
  · have h1 := h.2 a
    rw [← map_nsmul_eq_pow _ o'.etaA_add] at h1
    rw [← map_nsmul_eq_pow _ o''.etaA_add, e, ← Category.assoc, m.etaA, Category.assoc, h1, Category.assoc]

theorem descends_of_raises : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ : Level H) (B : BaseModel T l₀) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), 0 < n → l₀.Dvd l → l.A = 1 → IsDedFrac β → Raises B Y → Y.Descends := by
  intro h1 h2 h3 E _ _ _ H D Xo n N T hN l₀ B l c O _ β Y hn hd hA hβ hR
  obtain ⟨b, r, ν, hb, hlev, ⟨a⟩⟩ := hR
  obtain ⟨k, r₁, ν₁, hr₁, hk, hlev₁, hfin, -⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN l₀ l hd
  have hS : 0 < n * l₀.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l₀.three_le)
  have hD₀ : IsDedFrac B.β := isDedFrac_of_isInc l₀ _ 1 hS B.A_one rfl _ B.β_inc
  have hD₁ : IsDedFrac (k.comp B.β) :=
    isDedFrac_of_isInc l _ 1 hS hA rfl _ fun x => (hk (B.β x)).trans (B.β_inc x)
  have hsm : Smooth (Xo l).s := by
    have := (Xo l).smooth
    exact SmoothOfRelativeDimension.smooth D.dim _
  obtain ⟨C', ⟨a'⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ B.β _ _ _ (Xo l).s (Xo l).univ.t (k.comp B.β) B.C (RingHom.id _) k r₁ hr₁ ν₁
    hD₀ hD₁ (RingHom.comp_id _)
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm).2.1 hfin
  have hbβ : β.comp b = (IntermediateField.inclusion c.le).toRingHom.comp (k.comp B.β) := by
    refine RingHom.ext fun x => Subtype.ext ?_
    exact (hb x).trans ((hk (B.β x)).trans (B.β_inc x)).symm
  have hred : IsReduced ((Xo l).XF c) :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (pullback.snd _ _) inferInstance).1
  obtain ⟨ν₂, hν₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₁ Y.m0.toSABMap
  have hover : r ≫ (Xo l₀).s = (pullback.fst _ _ ≫ r₁) ≫ (Xo l₀).s := by
    have := mono_spMap_of_isDedFrac hD₀
    rw [← cancel_mono (spMap B.β), Category.assoc, ← Cpt_j_over B.C, ← Category.assoc, ← a.j_comm, Category.assoc,
      a.π_over, ← Category.assoc, Cpt_j_over, Category.assoc, ← spMap_comp, hbβ, spMap_comp, spMap_comp,
      Category.assoc, Category.assoc, reassoc_of% hr₁, pullback.condition_assoc]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.LevUniq.map_to_univ_unique h1 h2 h3 E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r _ ν ν₂ hred hover hlev
    (levComp_comp Y.m0 hlev₁ ν₂ hν₂)
  obtain ⟨h, mu', hh, -, -, hj, hφ, hf⟩ := GlobalTheory.Models.Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    B.C C' (ofModel Y) (RingHom.id _) b (IntermediateField.inclusion c.le).toRingHom r₁ ν₁ a' (pullback.fst _ _)
    Y.m0.toSABMap a.π a.mu a.π_over hβ hbβ pullback.condition
    (by rw [a.j_comm, e₁, Category.assoc]) (by rw [a.φ_comm, e₂, hν₂, Category.assoc])
  exact GlobalTheory.descends_of_above E H D l (Xo l) c O β Y _ (k.comp B.β) C' b ⟨h, hh, hf a.fin, mu', hj, hφ⟩ hD₁ hβ hbβ

end GlobalTheory.RaisedDescends

end
