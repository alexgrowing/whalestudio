import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTorsionLift
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevLift

theorem exists_eq_val_add {J : Type} {n : ℕ} [NeZero n] (a : J → ℤ) :
    ∃ b : J → ℤ, a = (fun i => (((a i : ZMod n)).val : ℤ)) + n • b :=
  ⟨fun i => a i / n, funext fun i => by
    rw [Pi.add_apply, Pi.smul_apply, ZMod.val_intCast, nsmul_eq_mul]
    exact (Int.emod_add_mul_ediv (a i) n).symm⟩

section Count

variable {G : Type} [CommGroup G] {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} [NeZero n] (f : (J → ℤ) → G)
  (hadd : ∀ a b, f (a + b) = f a * f b) (hker : ∀ a, f a = 1 ↔ ∃ b, a = n • b)
include hadd hker

theorem eq_val (a : J → ℤ) : f a = f (fun i => (((a i : ZMod n)).val : ℤ)) := by
  obtain ⟨b, hb⟩ := exists_eq_val_add (n := n) a
  conv_lhs => rw [hb]
  rw [hadd, (hker (n • b)).2 ⟨b, rfl⟩, _root_.mul_one]

theorem inj : Function.Injective (fun c : J → ZMod n => f (fun i => ((c i).val : ℤ))) := by
  intro c c' h
  simp only at h
  have h1 : f ((fun i => ((c i).val : ℤ)) - (fun i => ((c' i).val : ℤ))) = 1 := by
    have e := hadd ((fun i => ((c i).val : ℤ)) - (fun i => ((c' i).val : ℤ))) (fun i => ((c' i).val : ℤ))
    rw [sub_add_cancel, h] at e
    exact mul_eq_right.1 e.symm
  obtain ⟨b, hb⟩ := (hker _).1 h1
  funext i
  have e := congrFun hb i
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e
  have e2 := congrArg (fun z : ℤ => (z : ZMod n)) e
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul] at e2
  exact sub_eq_zero.1 e2

theorem card_eq (htors : ∀ a, f a ^ n = 1) (hsurj : ∀ x : G, x ^ n = 1 → ∃ a, f a = x) :
    Nat.card {x : G // x ^ n = 1} = n ^ Fintype.card J := by
  let F : (J → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨f (fun i => ((c i).val : ℤ)), htors _⟩
  have hF : Function.Bijective F := ⟨fun c c' e => inj f hadd hker (congrArg Subtype.val e), fun x => by
    obtain ⟨a, ha⟩ := hsurj x.1 x.2
    exact ⟨fun i => (a i : ZMod n), Subtype.ext (by rw [← ha, eq_val f hadd hker a])⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem surj (htors : ∀ a, f a ^ n = 1) (hcard : Nat.card {x : G // x ^ n = 1} = n ^ Fintype.card J) :
    ∀ x : G, x ^ n = 1 → ∃ a, f a = x := by
  intro x hx
  let F : (J → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨f (fun i => ((c i).val : ℤ)), htors _⟩
  have hFi : Function.Injective F := fun c c' e => inj f hadd hker (congrArg Subtype.val e)
  have hne : Nat.card {x : G // x ^ n = 1} ≠ 0 := by
    rw [hcard]; exact pow_ne_zero _ (NeZero.ne n)
  haveI : Finite {x : G // x ^ n = 1} := Nat.finite_of_card_ne_zero hne
  have hle : Nat.card {x : G // x ^ n = 1} ≤ Nat.card (J → ZMod n) := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  obtain ⟨c, hc⟩ := (hFi.bijective_of_nat_card_le hle).2 ⟨x, hx⟩
  exact ⟨_, congrArg Subtype.val hc⟩

end Count

end GlobalTheory.LevLift

namespace GlobalTheory.LevLift

theorem exists_level_lift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (βV : cycAway n →+* V) (π : V →+* K), Function.Surjective π → ∀ (c : SiegPre g n (zetaAway n) (spMap (π.comp βV))), c.Principal → ∀ (AV : Over (Sp V)) [GrpObj AV] [IsCommMonObj AV] (φ : c.A.left ⟶ AV.left) (φ₂ : (G2 c.A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV → IsGrpPullback c.A AV (spMap π) φ → IsSquare φ φ₂ → PV.IsLB → (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) → (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) → LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) → Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) → (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) → LBIso c.P (PV.pull φ₂) → ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp V)) ⟶ AV), (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ n = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp V) (β : cycAway n →+* k) (z : kˣ), x ≫ spMap βV = spMap β → (z : k) = β (zetaAway n) → (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ g' : Over.mk x ⟶ AV, g' ^ n = 1 → ∃ a, toUnit _ ≫ lev a = g') ∧ ∀ a b, Out.WeilIs AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b)))) ∧ ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (lev a).left := by
  intro g n hn3 hnodd K _ _ V _ _ _ _ hcV βV π hπ c hcP AV _ _ φ φ₂ PV hAV hφ hsq hPV hr₁ hr₂ hsym hamp hkerV hiso
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  have hnR : IsUnit (n : V) := by simpa using (isUnit_natCast hn0).map βV
  have hnΓ : IsUnit (n : Γ(Sp V, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    rwa [map_natCast] at this
  have hP : GlobalTheory.TChart.IsPPol AV PV := ⟨⟨hPV, hr₁, hr₂, hsym⟩, hamp, hkerV⟩

  have hζc : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  let ζU : (cycAway n)ˣ := (hζc.isUnit hn0).unit
  let ζR : Vˣ := Units.map βV.toMonoidHom ζU
  have hζR : IsPrimitiveRoot ζR n := IsPrimitiveRoot.coe_units_iff.1 (GlobalTheory.LevSpread.prim_map hn0 βV)

  have hdiag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((PV.pull (lift (𝟙 AV) (𝟙 AV)).left).pull φ) := by
    have ext2 : ∀ {X : Scheme.{0}} (u v : X ⟶ (G2 AV).left), u ≫ (fst AV AV).left = v ≫ (fst AV AV).left →
        u ≫ (snd AV AV).left = v ≫ (snd AV AV).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
    have d1 : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ (fst c.A c.A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have d2 : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ (snd c.A c.A).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
    have d1' : (lift (𝟙 AV) (𝟙 AV)).left ≫ (fst AV AV).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have d2' : (lift (𝟙 AV) (𝟙 AV)).left ≫ (snd AV AV).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
    have hd : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 AV) (𝟙 AV)).left := by
      apply ext2
      · rw [Category.assoc, hsq.1, ← Category.assoc, d1, Category.id_comp, Category.assoc, d1', Category.comp_id]
      · rw [Category.assoc, hsq.2, ← Category.assoc, d2, Category.id_comp, Category.assoc, d2', Category.comp_id]
    have h3 := GlobalTheory.ThetaAffineGlue.lbIso_pull hiso (lift (𝟙 c.A) (𝟙 c.A)).left
    rw [hd] at h3
    have hΔ := pull_isLB hPV (lift (𝟙 AV) (𝟙 AV)).left
    exact h3.trans (pull_isLB c.isLB _) (pull_isLB hPV _) (pull_isLB hΔ _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull
        (show LBIso (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) from
          LBIso.trans hΔ (pull_isLB hΔ _) hΔ (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ)
            (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ))) φ).symm

  have hL := fun a => GlobalTheory.TorsLiftComplete.existsUnique_torsion_lift V K n hcV hnR π hπ c.A AV φ hAV hφ (c.lev a)
    (c.lev_tors a)
  choose σ hσ using fun a => (hL a).exists
  have hσn : ∀ a, σ a ^ n = 1 := fun a => (hσ a).1
  have hcomp : ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (σ a).left := fun a => (hσ a).2
  let E := GlobalTheory.ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  let T₁ : Over (Sp V) := Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap π)
  have hσx : ∀ a, toUnit T₁ ≫ σ a = E (c.lev a) := fun a => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.pushEquiv_left, hcomp]
    exact congrArg (· ≫ (σ a).left) (Category.id_comp _)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp V))).left := inferInstanceAs (PreconnectedSpace (Sp V))
  have inj : ∀ (T : Over (Sp V)) [Nonempty T.left] (s s' : 𝟙_ (Over (Sp V)) ⟶ AV), s ^ n = 1 → s' ^ n = 1 →
      toUnit T ≫ s = toUnit T ≫ s' → s = s' := fun T _ s s' hs hs' h =>
    GlobalTheory.LevSpread.eq_of_comp_eq AV hAV hnΓ (𝟙_ _) s s' hs hs' T (toUnit T) h
  haveI : Nonempty T₁.left := inferInstanceAs (Nonempty (Sp K))
  have hadd : ∀ a a', σ (a + a') = σ a * σ a' := fun a a' =>
    inj T₁ _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, c.lev_add, map_mul])
  have one_iff : ∀ (T : Over (Sp V)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ σ a = 1 := fun T _ a =>
    ⟨fun h => inj T (σ a) 1 (hσn a) (one_pow n) (h.trans (MonObj.comp_one _).symm),
      fun h => by rw [h, MonObj.comp_one]⟩

  let iK : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap iK
  obtain ⟨g1, g2, g3⟩ := c.geom (AlgebraicClosure K) x₀ ((iK.comp π).comp βV)
    (Units.map ((iK.comp π).comp βV).toMonoidHom ζU) (by rw [← Spec.map_comp]; rfl) rfl
  let T₀ : Over (Sp V) := Over.mk ((Over.mk x₀).hom ≫ spMap π)
  haveI : Nonempty T₀.left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  have push : ∀ a, GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀) (toUnit _ ≫ c.lev a) = toUnit T₀ ≫ σ a := fun a => by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, hcomp,
      GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.toUnit_left']
    exact (Category.assoc _ _ _).symm
  have hker : ∀ a, σ a = 1 ↔ ∃ b, a = n • b := fun a => by
    rw [← one_iff T₀, ← push, map_eq_one_iff _ (GlobalTheory.ObjPull.pushEquiv hφ _).injective]
    exact g1 a

  haveI : ConnectedSpace (Sp V) := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing V
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim_of_connected AV hAV
  have kerAt : ∀ (T : Over (Sp V)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ ∃ b, a = n • b := fun T _ a => by
    rw [one_iff T]; exact hker a
  have addAt : ∀ (T : Over (Sp V)) a a', toUnit T ≫ σ (a + a') = (toUnit T ≫ σ a) * (toUnit T ≫ σ a') :=
    fun T a a' => by rw [hadd, MonObj.comp_mul]
  have torsAt : ∀ (T : Over (Sp V)) a, (toUnit T ≫ σ a) ^ n = 1 := fun T a => by
    rw [← MonObj.comp_pow, hσn, MonObj.comp_one]
  have surj₀ : ∀ gg : T₀ ⟶ AV, gg ^ n = 1 → ∃ a, toUnit T₀ ≫ σ a = gg := fun gg hg => by
    obtain ⟨a, ha⟩ := g2 ((GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀)).symm gg)
      (by rw [← map_pow, hg, map_one])
    exact ⟨a, by rw [← push, ha, MulEquiv.apply_symm_apply]⟩
  have card₀ := card_eq (fun a => toUnit T₀ ≫ σ a) (addAt T₀) (kerAt T₀) (torsAt T₀) surj₀
  have cardd := GlobalTheory.TorsionCover.card_torsion AV hAV hd ((Over.mk x₀).hom ≫ spMap π)
    (GlobalTheory.TorsionCover.natCast_ne_zero hnΓ ((Over.mk x₀).hom ≫ spMap π))
  have hdg : d = g := by
    have e : n ^ (2 * d) = n ^ (2 * g) := by
      rw [← cardd, show 2 * g = Fintype.card (Fin g ⊕ Fin g) by simp [two_mul]]
      exact card₀
    have := Nat.pow_right_injective (show 2 ≤ n by omega) e
    omega
  subst hdg
  refine ⟨σ, hadd, hσn, fun k _ _ x β z hxβ hz => ?_, hcomp⟩
  obtain ⟨ρ, rfl⟩ : ∃ ρ : V →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hβ : β = ρ.comp βV := by
    have e : spMap (ρ.comp βV) = spMap β := by rw [← hxβ]; exact Spec.map_comp _ _
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  have hzU : z = Units.map ρ.toMonoidHom ζR := Units.ext (by rw [hz, hβ]; rfl)
  subst hzU
  haveI : Nonempty (Over.mk (spMap ρ)).left := inferInstanceAs (Nonempty (Sp k))
  refine ⟨fun a => kerAt _ a, fun gg hg => ?_, fun a a' => ?_⟩
  · have cardk := GlobalTheory.TorsionCover.card_torsion AV hAV hd (spMap ρ) (GlobalTheory.TorsionCover.natCast_ne_zero hnΓ (spMap ρ))
    exact surj (fun a => toUnit (Over.mk (spMap ρ)) ≫ σ a) (addAt _) (kerAt _) (torsAt _)
      (by rw [cardk]; simp [two_mul]) gg hg
  · have H' := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm (Sp V) (Sp K) AV c.A (spMap π) φ
      (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) (pull_isLB hPV _)
      (pull_isLB c.isLB _) hφ hdiag (Over.mk x₀) (n : ℤ) _ _ (toUnit T₀ ≫ σ a) (toUnit T₀ ≫ σ a') _
      (by rw [← push]; rfl) (by rw [← push]; rfl)).1 (g3 a a')
    have ht : (Over.mk x₀).hom ≫ spMap π = spMap (iK.comp π) := by
      show x₀ ≫ spMap π = _
      rw [← Spec.map_comp]; rfl
    have hu : (Units.map ((iK.comp π).comp βV).toMonoidHom ζU) ^ (2 * omegaStd a a') =
        Units.map (iK.comp π).toMonoidHom (ζR ^ (2 * omegaStd a a')) := by
      rw [map_zpow]; rfl
    rw [hu] at H'
    simp only [T₀] at H'
    rw [ht] at H'
    have H'' := GlobalTheory.LevSpread.l3 V AV hAV PV hP n (by omega) hnR (σ a) (σ a') (hσn a) (hσn a') ζR hζR
      (2 * omegaStd a a') (AlgebraicClosure K) (iK.comp π) H' k ρ
    rw [← map_zpow]
    exact H''

end GlobalTheory.LevLift
