import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CoefUpTo

theorem coef_upTo : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') (s : R), (∀ T, UpTo s (α.app T).hom) →
    ∀ n, UpTo (s ^ 2) ((Mor.ofNatTrans α).pull n) := by
  intro R _ C _ F F' α s h n
  have inj : ∀ k (f : Cn F k), (Mor.ofNatTrans α).pullC k f = 0 → s • f = 0 := fun k f hf =>
    funext fun c => (h _).1 (f c) (congrFun hf c)
  have surj : ∀ k (g : Cn F' k), ∃ f : Cn F k, (Mor.ofNatTrans α).pullC k f = s • g := fun k g => by
    choose f hf using fun c : ComposableArrows C k => (h (c.obj (Fin.last k))).2 (g c)
    exact ⟨f, funext hf⟩
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
    have hz : (cx F').d n ((Mor.ofNatTrans α).pullC n a) = 0 := by
      have ha' : d F n a = 0 := ha
      change d F' n _ = 0
      rw [Mor.d_pullC, ha', map_zero]
    have hx' : (cx F').cls ((Mor.ofNatTrans α).pullC n a) hz = 0 := hx
    rw [(CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1] at hx'
    have hd : (cx F).d n ((s ^ 2) • a) = 0 := by rw [map_smul, ha, smul_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj (cx F) n).2.2.2.2 (s ^ 2) a ha hd, (CrystallineSemistableComparison.P.cls_surj (cx F) n).2.1]
    cases n with
    | zero =>
      have h0 : (Mor.ofNatTrans α).pullC 0 a = 0 := hx'
      have h1 : (s ^ 2) • a = 0 := by rw [pow_two, mul_smul, inj 0 a h0, smul_zero]
      rw [h1]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨g', hg'⟩ := hx'
      have hg'' : d F' n g' = (Mor.ofNatTrans α).pullC (n + 1) a := hg'
      obtain ⟨g, hg⟩ := surj n g'
      have h0 : (Mor.ofNatTrans α).pullC (n + 1) (s • a - d F n g) = 0 := by
        rw [map_sub, ← Mor.d_pullC, hg, map_smul, map_smul, hg'']
        simp
      have h1 := inj _ _ h0
      rw [smul_sub, sub_eq_zero] at h1
      refine ⟨s • g, ?_⟩
      change d F n (s • g) = (s ^ 2) • a
      rw [map_smul, ← h1, pow_two, mul_smul]
  · obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F') n).1 y
    have hb' : d F' n b = 0 := hb
    obtain ⟨f, hf⟩ := surj n b
    have h0 : (Mor.ofNatTrans α).pullC (n + 1) (d F n f) = 0 := by
      rw [← Mor.d_pullC, hf, map_smul, hb', smul_zero]
    have h1 : d F n (s • f) = 0 := by rw [map_smul]; exact inj _ _ h0
    have hd : (cx F').d n ((s ^ 2) • b) = 0 := by rw [map_smul, hb, smul_zero]
    have e : (Mor.ofNatTrans α).pullC n (s • f) = (s ^ 2) • b := by
      rw [map_smul, hf, pow_two, mul_smul]
    refine ⟨(cx F).cls (s • f) h1, ?_⟩
    rw [← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.2 (s ^ 2) b hb hd]
    change (cx F').cls ((Mor.ofNatTrans α).pullC n (s • f)) _ = _
    simp only [e]

end GlobalTheory.CompanionTheory.CoefUpTo
