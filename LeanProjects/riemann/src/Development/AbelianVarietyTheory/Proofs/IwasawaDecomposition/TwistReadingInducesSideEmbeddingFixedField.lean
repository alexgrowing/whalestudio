import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem mem_range_map_iff_of_isLocalHom {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) [IsLocalHom f] (hf : Function.Injective f) (t : FractionRing A) :
    IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t ∈ (algebraMap B (FractionRing B)).range ↔
      t ∈ (algebraMap A (FractionRing A)).range := by
  have hmap : ∀ a : A, IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf (algebraMap A _ a) =
      algebraMap B _ (f a) := fun a => by simp [IsFractionRing.map]
  constructor
  · rintro ⟨c, hc⟩
    by_cases ht : t = 0
    · exact ⟨0, by rw [ht, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger A t with ⟨a, ha⟩ | ⟨m, hm⟩
    · exact ⟨a, ha⟩
    · have h1 : IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t *
          IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      rw [← hc, ← hm, hmap, ← map_mul] at h1
      have h2 : c * f m = 1 := IsFractionRing.injective B (FractionRing B) (by rw [h1, map_one])
      have hu : IsUnit m := (isUnit_map_iff f m).1 (IsUnit.of_mul_eq_one_right c h2)
      refine ⟨((hu.unit⁻¹ : Aˣ) : A), ?_⟩
      rw [← inv_inv t, ← hm]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul]
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨f a, (hmap a).symm⟩

end GlobalTheory.LevCmp

namespace GlobalTheory.LevCmp

theorem reading_sidePl_emb : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), GlobalTheory.HeightCounting.SidePl D v i b ∧ (∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x))) ∧ ∀ (h : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))))) (x : ↥D.LL0), ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) h (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := by
  intro D i k b v ρ
  haveI := GlobalTheory.TwistChoice.isLocalHom_phiK i k
  haveI := ρ.loc
  have hinj : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp (BlochKatoReduction.Gen.phiK D.ntw i k)) :=
    ρ.inj.comp ((D.ntw.Ok_inj i k).comp (D.ntw.O_inj i))
  have hmap : ∀ a : D.ntw.O0 i, IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) hinj
      (algebraMap _ _ a) = algebraMap ρ.Oe _ (algebraMap _ ρ.Oe (BlochKatoReduction.Gen.phiK D.ntw i k a)) := fun a => by
    simp [IsFractionRing.map]
  have key : ∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) =
      IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) hinj
        (GlobalTheory.TwistChoice.sideEmb i b x) := by
    intro x
    obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (GlobalTheory.TwistChoice.sideEmb i b x)
    have hz0 : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
    have hside : GlobalTheory.TwistChoice.sideEmb i b x * algebraMap _ (FractionRing (D.ntw.O0 i)) z =
        algebraMap _ (FractionRing (D.ntw.O0 i)) y := by
      rw [← hyz, div_mul_cancel₀ _ hz0]
    have h1 := ρ.emb_side x y z hside
    have hz' : algebraMap ρ.Oe (FractionRing ρ.Oe) (algebraMap _ ρ.Oe (BlochKatoReduction.Gen.phiK D.ntw i k z)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), ← RingHom.comp_apply,
        map_eq_zero_iff _ hinj]
      exact nonZeroDivisors.ne_zero hz
    rw [← hyz, map_div₀, hmap, hmap, eq_div_iff hz']
    exact h1
  have hside : ∀ x : ↥D.LL0, GlobalTheory.TwistChoice.sideEmb i b x =
      (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := fun x => by
    cases b <;> rfl
  refine ⟨fun x => ?_, fun x => ?_, fun h x => ?_⟩
  · rw [ρ.emb_w, key, ← hside]
    exact mem_range_map_iff_of_isLocalHom _ hinj _
  · rw [key]
    obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (GlobalTheory.TwistChoice.sideEmb i b x)
    have e : GlobalTheory.SeriesTie.sideEmb D.ntw i b x = IsFractionRing.map (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) (GlobalTheory.TwistChoice.sideEmb i b x) := by
      cases b <;> rfl
    rw [e, ← hyz]
    simp [map_div₀, IsFractionRing.map, NX.toKk, BlochKatoReduction.Gen.phiK]
  · rw [key, ← hside]
    rfl

end GlobalTheory.LevCmp
