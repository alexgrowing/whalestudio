import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsStableFlag
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotGlobalHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.ES.IsogDVR

theorem isPullback_kernel_of_kernelPair {S : Scheme.{0}} {A H B : Over S} [GrpObj A] [GrpObj B] (i : H ⟶ A)
    [Mono i] (q : A ⟶ B) [IsMonHom q] (h : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q) :
    IsPullback i (toUnit H) q η[B] := by
  have hi : i ≫ q = 1 := by
    have := congrArg (fun u => lift (𝟙 H) (1 : H ⟶ A) ≫ u) h.w
    simp only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, Category.id_comp, _root_.mul_one,
      MonObj.one_comp] at this
    exact this
  refine ⟨⟨by rw [hi, Hom.one_def]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst 1 (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
      ≫ fst H A) (fun s => ?_) (fun s => toUnit_unique _ _) (fun s l h1 _ => ?_)⟩⟩
  · have h1 := h.lift_fst s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    have h2 := h.lift_snd s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    rw [MonObj.comp_mul, h2, _root_.mul_one] at h1
    rw [Category.assoc, h1]
  · have h1' := h.lift_fst s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    have h2 := h.lift_snd s.fst 1
      (by rw [s.condition, MonObj.one_comp, Hom.one_def, toUnit_unique s.snd (toUnit _)])
    rw [MonObj.comp_mul, h2, _root_.mul_one] at h1'
    rw [← cancel_mono i, Category.assoc, h1', h1]

open GlobalTheory.TorsionKernelModel in

theorem exists_model (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (A₀ B₀ : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] (φ : A₀.left ⟶ A.left) (ψ : A₀ ⟶ B₀) (n : ℕ)
    (hφ : IsGrpPullback A₀ A (spMap (algebraMap R K)) φ) (hB : IsAbelianScheme B₀) [IsMonHom ψ] [IsFinite ψ.left]
    [Flat ψ.left] [Surjective ψ.left] (hn : 1 ≤ n)
    (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A₀), x ≫ ψ = 1 → x ^ n = 1) :
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (φB : B₀.left ⟶ B.left), IsAbelianScheme B ∧
      IsGrpPullback B₀ B (spMap (algebraMap R K)) φB := by
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  have := hA.proper
  have := hB.proper
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback A _) hφ
  have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
  obtain ⟨Z, _, i, _, hi, hZ⟩ := exists_kernel (a.hom ≫ ψ)
  obtain ⟨Ga, io, e, _, _, he⟩ := IsogenyModel.exists_flat_closure R K A Z i hi
  obtain ⟨_, _, -⟩ := exists_grpObj_of_flat_closed _ A Ga io Z i e he
  have hkill : (Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom ≫ ψ = toUnit _ ≫ η[B₀] := by
    rw [← he, Category.assoc, hZ.w, comp_toUnit_assoc]
  have hpow : io ^ n = 1 := by
    apply ExtUnique.pullback_map_injective (spMap (algebraMap R K))
    have h₁ := hker _ ((Over.pullback (spMap (algebraMap R K))).map io ≫ a.hom) (by
      rw [Category.assoc, hkill, Hom.one_def])
    rw [← MonObj.pow_comp, ← MonObj.one_comp a.hom, cancel_mono] at h₁
    exact (map_pow (Over.pullback (spMap (algebraMap R K))).homMonoidHom io n).trans
      (h₁.trans (map_one (Over.pullback (spMap (algebraMap R K))).homMonoidHom).symm)
  have := (GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul _ A hA n hn).1
  have hfin : IsFinite Ga.hom := isFinite_of_pow_eq_one io n hpow
  have hm : Mono io := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))
  obtain ⟨B, _, q, hab, _, hq₁, hq₂, hq₃, hq⟩ := GlobalTheory.IwLevel.quotGlobal_holds _ A Ga io hA ‹_› hm hfin ‹_›
  have hq' := isPullback_kernel_baseChange (spMap (algebraMap R K)) (isPullback_kernel_of_kernelPair io q hq)
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨β, _, hβ⟩ := flatQuotient_iso_of_same_kernel _ _ _ _ _ _
    ((Over.pullback (spMap (algebraMap R K))).map q) ((Over.pullback (spMap (algebraMap R K))).map io) (a.hom ≫ ψ) i
    inferInstance inferInstance
    (MorphismProperty.overPullbackMap (P := @Flat) _ q hq₂)
    (MorphismProperty.overPullbackMap (P := @Surjective) _ q hq₃)
    (MorphismProperty.overPullbackMap (P := @QuasiCompact) _ q hqc) hq' inferInstance inferInstance
    (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
    (by rw [Over.comp_left]; infer_instance) hZ
    (by rw [← e.inv_hom_id_assoc i, he, Category.assoc, hq'.w, comp_toUnit_assoc]) hkill
  exact ⟨B, _, β.hom.left ≫ pullback.fst B.hom (spMap (algebraMap R K)), hab,
    ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback B _)).congr (Category.id_comp _) rfl⟩

theorem exists_obj {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (v : Sp V ⟶ Sp R) (s : Sp K ⟶ Sp R) (hs : s = spMap (algebraMap V K) ≫ v) (o : Obj b N s)
    (G : Over (Sp V)) [GrpObj G] (φ : o.A.left ⟶ G.left) (hG : IsAbelianScheme G)
    (h : IsGrpPullback o.A G (spMap (algebraMap V K)) φ) :
    ∃ o' : Obj b N v, Nonempty (ObjMap o o' (spMap (algebraMap V K))) := by
  obtain ⟨g, rfl⟩ : ∃ g : R →+* V, v = spMap g := ⟨(Spec.preimage v).hom, (Spec.map_preimage v).symm⟩
  have e : s = spMap ((algebraMap V K).comp g) := by
    rw [hs, ← Spec.map_comp]; rfl
  subst e
  exact GlobalTheory.HTObjExt.extends_obj p D R b N V K g o G φ hG h

theorem exists_isPIsog_extend_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (v : Sp V ⟶ Sp R) (o : Obj b N v) (o₀ o₀' : Obj b N (spMap (algebraMap V (FractionRing V)) ≫ v)) (m : ObjMap o₀ o (spMap (algebraMap V (FractionRing V)))) (ψ₀ : o₀.A ⟶ o₀'.A), IsPIsog c o₀ o₀' ψ₀ → ∃ (o' : Obj b N v) (m' : ObjMap o₀' o' (spMap (algebraMap V (FractionRing V)))) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := by
  intro p _ D R _ b N hN hNp c V _ _ _ v o o₀ o₀' m ψ₀ h
  have hc := h.pos
  obtain ⟨⟨k, hk⟩, hhom, -, -, -, ψ', hhom', h1, h2⟩ := id h
  obtain ⟨hf, hfl⟩ := GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse _ o₀.A o₀'.A o₀.ab o₀'.ab ψ₀ ψ' c hc.ne'
    hhom hhom' h1 h2
  have hsc : Surjective (ψ'.left ≫ ψ₀.left) := by
    rw [← Over.comp_left, h2]; exact GlobalTheory.AbelianLimit.surjective_pow o₀'.A o₀'.ab c hc
  have hs : Surjective ψ₀.left := Surjective.of_comp ψ'.left ψ₀.left
  obtain ⟨B, _, φB, hB, hφB⟩ := exists_model V (FractionRing V) o.A o.ab o₀.A o₀'.A m.φ ψ₀ c m.cart o₀'.ab hc
    (fun T x hx => by
      have : x ≫ ψ₀ ≫ ψ' = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
      rwa [h1, MonObj.comp_pow, Category.comp_id] at this)
  obtain ⟨o', ⟨m'⟩⟩ := exists_obj V (FractionRing V) v _ rfl o₀' B φB hB hφB
  have hopen : IsOpenImmersion (spMap (algebraMap V (FractionRing V))) :=
    GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing V (FractionRing V)
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing V (FractionRing V)
  have hdom : IsDominant (spMap (algebraMap V (FractionRing V))) := inferInstance
  obtain ⟨ψ, hψ, hm⟩ := GlobalTheory.UPel.HT.ES.PIsogExt.exists_isPIsog_extend p D R b N hN hNp 0 c
    ⟨k, hk, fun h => absurd h (lt_irrefl 0)⟩ _ _ (spMap (algebraMap V (FractionRing V))) _ v hopen hdom inferInstance
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).2) (fun y => inferInstance) o o' o₀ o₀' m m' ψ₀ h
  exact ⟨o', m', ψ, hψ, hm⟩

end GlobalTheory.UPel.HT.ES.IsogDVR
