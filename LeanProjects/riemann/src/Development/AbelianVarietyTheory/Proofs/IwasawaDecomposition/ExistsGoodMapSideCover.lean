import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalCoeffF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LvCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem obj_ext {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    {o o' : Obj D l b s} (ht : o.t = o'.t) (he : HEq o.eta o'.eta) (heA : HEq o.etaA o'.etaA) : o = o' := by
  cases o; cases o'
  cases ht
  cases he
  cases heA
  rfl

theorem etaA_eq_eta {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} [IsReduced S]
    {s : S ⟶ Sp B} (o : Obj D l b s) (hM : l.M ∣ l.A) (a : D.La) :
    o.etaA ((l.A / l.M) • (vOf l • a)) = o.eta a := by
  have := o.proper
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  have ea : o.eta a = o.eta (vOf l • a) := by
    conv_lhs => rw [← one_smul (𝓞 E) a, ← uOf_add_vOf l, add_smul, o.eta_add,
      o.eta_ker _ (Submodule.smul_mem_smul (uOf_mem l) Submodule.mem_top), _root_.one_mul]
  rw [ea]
  refine Over.OverMorphism.ext (ext_of_fromSpecResidueField_eq _ _ o.t.G.hom Set.univ dense_univ (fun x _ => ?_)
    ((Over.w _).trans (Over.w _).symm))
  let k := AlgebraicClosure (S.residueField x)
  let i : Sp k ⟶ Spec (S.residueField x) := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k))
  have : Flat i := (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective i := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim (α := PrimeSpectrum _) _ _⟩⟩
  have : Epi i := Flat.epi_of_flat_of_surjective _
  obtain ⟨-, I, -, hA, hη⟩ := o.geom k (i ≫ S.fromSpecResidueField x)
    (Spec.preimage ((i ≫ S.fromSpecResidueField x) ≫ s)).hom (Spec.map_preimage _).symm
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hq : 0 < l.A / l.M := Nat.div_pos (Nat.le_of_dvd l.A_pos hM) hM0
  have e : toUnit (Over.mk (i ≫ S.fromSpecResidueField x)) ≫ o.etaA ((l.A / l.M) • (vOf l • a)) =
      toUnit _ ≫ o.eta (vOf l • a) := by
    rw [hA, hη _ (Submodule.smul_mem_smul (vOf_mem l) Submodule.mem_top),
      GlobalTheory.ObjLower.map_nsmul_of_add _ (I.add _), ← I.tower l.M _ hM0 hq, Nat.mul_div_cancel' hM]
  rw [← cancel_epi i, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun q => q.left) e

theorem reM_reM {l l' : Level H} {B : Type} [CommRing B] {b : Base l B} {b' : Base l' B} {S : Scheme.{0}} [IsReduced S]
    {s : S ⟶ Sp B} (o : Obj D l b s) (hAA : l'.A = l.A) (hM : l.M ∣ l.A) (hM' : l'.M ∣ l.A) (hA : l'.A ∣ l.A)
    (hρ : b'.ρ = b.ρ) (hζ : b'.ζ = b.ζ ^ (l.A / l'.A)) (hM₂ : l.M ∣ l'.A) (hA₂ : l.A ∣ l'.A) (hρ₂ : b.ρ = b'.ρ)
    (hζ₂ : b.ζ = b'.ζ ^ (l'.A / l.A)) :
    reM (reM o hM' hA hρ hζ) hM₂ hA₂ hρ₂ hζ₂ = o := by
  refine obj_ext rfl (heq_of_eq (funext fun a => ?_)) (heq_of_eq (funext fun a => ?_))
  · show o.etaA ((l.A / l'.A) • ((l'.A / l.M) • (vOf l • a))) = o.eta a
    rw [hAA, Nat.div_self l.A_pos, one_smul]
    exact etaA_eq_eta o hM a
  · show o.etaA ((l.A / l'.A) • ((l'.A / l.A) • a)) = o.etaA a
    rw [hAA, Nat.div_self l.A_pos, one_smul, one_smul]

theorem side_goodMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l₁ l₂ : Level H)
    (Xo : Moduli D (GlobalTheory.LvCover.top l₁ l₂)) (Xs : Moduli D (GlobalTheory.LvCover.side l₁ l₂)) (c₁ : Coeff l₁) (c₂ : Coeff l₂)
    (Y : GlobalTheory.TorRef.GMod Xo (GlobalTheory.LvCover.coeffTop c₁ c₂)) (Ys : GlobalTheory.TorRef.GMod Xs (GlobalTheory.LvCover.coeffSide c₁ c₂)),
    ∃ r, GlobalTheory.LvCover.GoodMap (le_refl (GlobalTheory.LvCover.coeffF c₁ c₂)) Y Ys r := by
  intro E _ _ _ H D l₁ l₂ Xo Xs c₁ c₂ Y Ys
  have : IsReduced Xo.X := by
    have := Xo.smooth
    have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
    exact isReduced_of_smooth Xo.s
  have : IsReduced Xs.X := by
    have := Xs.smooth
    have : Smooth Xs.s := SmoothOfRelativeDimension.smooth D.dim _
    exact isReduced_of_smooth Xs.s
  have hζs : (baseKA (side l₁ l₂)).ζ = (baseKA (top l₁ l₂)).ζ ^ ((top l₁ l₂).A / (side l₁ l₂).A) := by
    rw [show (top l₁ l₂).A / (side l₁ l₂).A = 1 from Nat.div_self (top l₁ l₂).A_pos, pow_one]; rfl
  have hζt : (baseKA (top l₁ l₂)).ζ = (baseKA (side l₁ l₂)).ζ ^ ((side l₁ l₂).A / (top l₁ l₂).A) := by
    rw [show (side l₁ l₂).A / (top l₁ l₂).A = 1 from Nat.div_self (top l₁ l₂).A_pos, pow_one]; rfl
  obtain ⟨α, ⟨hα, ⟨mα⟩⟩, -⟩ := Xs.rep Xo.X Xo.s ‹_›
    (reM Xo.univ (l' := side l₁ l₂) (b' := baseKA (side l₁ l₂)) (M_dvd_side l₁ l₂) dvd_rfl rfl hζs)
  obtain ⟨β, ⟨hβ, ⟨mβ⟩⟩, -⟩ := Xo.rep Xs.X Xs.s ‹_›
    (reM Xs.univ (l' := top l₁ l₂) (b' := baseKA (top l₁ l₂)) (M_dvd_top l₁ l₂) dvd_rfl rfl hζt)
  have hαβ : α ≫ β = 𝟙 _ := by
    obtain ⟨f, -, hf⟩ := Xo.rep Xo.X Xo.s ‹_› Xo.univ
    obtain ⟨u⟩ := GlobalTheory.LevelQuotRep.obj_comp (reMap mα (l' := top l₁ l₂) (b' := baseKA (top l₁ l₂)) (b₀' := baseKA (top l₁ l₂)) (M_dvd_top l₁ l₂) dvd_rfl rfl hζt rfl hζt) mβ
    have u' : ObjMap Xo.univ Xo.univ (α ≫ β) := cast (congrArg (fun z => ObjMap z Xo.univ (α ≫ β))
      (reM_reM Xo.univ (l' := side l₁ l₂) (b' := baseKA (side l₁ l₂)) rfl (M_dvd_top l₁ l₂) (M_dvd_side l₁ l₂) dvd_rfl rfl hζs (M_dvd_top l₁ l₂) dvd_rfl rfl hζt)) u
    obtain ⟨v⟩ := GlobalTheory.LevelQuotRep.obj_cancel u' u' (𝟙 _) (Category.id_comp _)
    rw [hf _ ⟨by rw [Category.assoc, hβ]; exact hα, ⟨u'⟩⟩, hf _ ⟨Category.id_comp _, ⟨v⟩⟩]
  have hβα : β ≫ α = 𝟙 _ := by
    obtain ⟨f, -, hf⟩ := Xs.rep Xs.X Xs.s ‹_› Xs.univ
    obtain ⟨u⟩ := GlobalTheory.LevelQuotRep.obj_comp (reMap mβ (l' := side l₁ l₂) (b' := baseKA (side l₁ l₂)) (b₀' := baseKA (side l₁ l₂)) (M_dvd_side l₁ l₂) dvd_rfl rfl hζs rfl hζs) mα
    have u' : ObjMap Xs.univ Xs.univ (β ≫ α) := cast (congrArg (fun z => ObjMap z Xs.univ (β ≫ α))
      (reM_reM Xs.univ (l' := top l₁ l₂) (b' := baseKA (top l₁ l₂)) rfl (M_dvd_side l₁ l₂) (M_dvd_top l₁ l₂) dvd_rfl rfl hζt (M_dvd_side l₁ l₂) dvd_rfl rfl hζs)) u
    obtain ⟨v⟩ := GlobalTheory.LevelQuotRep.obj_cancel u' u' (𝟙 _) (Category.id_comp _)
    rw [hf _ ⟨by rw [Category.assoc, hα]; exact hβ, ⟨u'⟩⟩, hf _ ⟨Category.id_comp _, ⟨v⟩⟩]
  obtain ⟨r, hr1, hr2⟩ : ∃ r : Xo.XF (coeffTop c₁ c₂) ⟶ Xs.XF (coeffSide c₁ c₂),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ α ∧ r ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift (pullback.fst _ _ ≫ α) (pullback.snd _ _) (by rw [Category.assoc, hα]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨r', hr'1, hr'2⟩ : ∃ r' : Xs.XF (coeffSide c₁ c₂) ⟶ Xo.XF (coeffTop c₁ c₂),
      r' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ r' ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _) (by rw [Category.assoc, hβ]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have : IsIso r := ⟨r', pullback.hom_ext (by rw [Category.assoc, hr'1, ← Category.assoc, hr1, Category.assoc, hαβ,
      Category.comp_id, Category.id_comp]) (by rw [Category.assoc, hr'2]; exact hr2.trans (Category.id_comp _).symm),
    pullback.hom_ext (by rw [Category.assoc, hr1, ← Category.assoc, hr'1, Category.assoc, hβα,
      Category.comp_id, Category.id_comp]) (by rw [Category.assoc, hr2]; exact hr'2.trans (Category.id_comp _).symm)⟩
  obtain ⟨n, -⟩ := GlobalTheory.LevelCover.sab_comp Y.m0.toSABMap mα.toSABMap hr1.symm
  obtain ⟨m', -⟩ := GlobalTheory.LevelCover.sab_cancel Ys.m0.toSABMap n r rfl
  refine ⟨r, ⟨(GlobalTheory.ShFam.TwMap.reflEquiv _ _ _).symm m'⟩, r.surjective, ?_⟩
  exact hr2.trans ((Category.comp_id _).symm.trans (congrArg (fun g => pullback.snd _ _ ≫ g)
    (GlobalTheory.LevelCover.spMap_inclusion_self (le_refl (coeffF c₁ c₂))).symm))

end GlobalTheory.LvCover
