import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSemiAbelianHomRetractStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTorsionFamiliesEqualLocusOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSymplecticLevelLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusKernelKilledSymmetricBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsFormulasOfIdempotentImagePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEndomorphismImageCommutesBaseChangeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdemLocus

section Help
variable {S S' : Scheme.{0}}

theorem secPull_congr {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hp : IsGrpPullback A' A f φ) {x y : 𝟙_ (Over S) ⟶ A} (hxy : f ≫ x.left = f ≫ y.left) :
    GlobalTheory.SiegelPull.secPull hp x = GlobalTheory.SiegelPull.secPull hp y := by
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · rw [GlobalTheory.SiegelPull.secPull_left, GlobalTheory.SiegelPull.secPull_left, hxy]
  · rw [Over.w (GlobalTheory.SiegelPull.secPull hp x), Over.w (GlobalTheory.SiegelPull.secPull hp y)]

theorem secPull_map (f : S' ⟶ S) {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
    (m : G ⟶ A) (x : 𝟙_ (Over S) ⟶ G) :
    GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback f G) x ≫ (Over.pullback f).map m =
      GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback f A) (x ≫ m) := by
  apply Over.OverMorphism.ext
  apply (Pdiv.PullbackComparison.isGrpPullback f A).1.hom_ext
  · rw [GlobalTheory.SiegelPull.secPull_left, Over.comp_left, Category.assoc]
    show _ ≫ _ ≫ pullback.fst A.hom f = _
    rw [Pdiv.PullbackComparison.pullback_map_left_fst', ← Category.assoc]
    show (_ ≫ Pdiv.PullbackComparison.pφ f G) ≫ _ = _
    rw [GlobalTheory.SiegelPull.secPull_left, Over.comp_left, Category.assoc]
  · rw [Over.w, Over.w]

theorem secPull_prod {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hp : IsGrpPullback A' A f φ) {n : ℕ} (y : Fin n → (𝟙_ (Over S) ⟶ A)) :
    GlobalTheory.SiegelPull.secPull hp (List.ofFn y).prod = (List.ofFn fun k => GlobalTheory.SiegelPull.secPull hp (y k)).prod := by
  apply GlobalTheory.SiegelPull.push_injective hp
  rw [GlobalTheory.SiegelPull.push_secPull', GlobalTheory.comp_list_prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  exact (GlobalTheory.SiegelPull.push_secPull' hp (y k)).symm

end Help

end GlobalTheory.IdemLocus

namespace GlobalTheory.IdemLocus

theorem image_bundle_rig {S : Scheme.{0}} (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 A).left) (inc : G ⟶ A) [IsMonHom inc]
    (r₁ : ∃ s : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, s.IsGen)
    (r₂ : ∃ s : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, s.IsGen)
    (sy : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    (∃ s : ((P.pull (inc ⊗ₘ inc).left).pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) ∧
    (∃ s : ((P.pull (inc ⊗ₘ inc).left).pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) ∧
    LBIso (P.pull (inc ⊗ₘ inc).left) ((P.pull (inc ⊗ₘ inc).left).pull (lift (snd G G) (fst G G)).left) := by
  have e₁ : (lift (1 : G ⟶ G) (𝟙 G)).left ≫ (inc ⊗ₘ inc).left = inc.left ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [lift_map, comp_lift, MonObj.one_comp, MonObj.comp_one]
  have e₂ : (lift (𝟙 G) (1 : G ⟶ G)).left ≫ (inc ⊗ₘ inc).left = inc.left ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [lift_map, comp_lift, MonObj.one_comp, MonObj.comp_one]
  have e₃ : (lift (snd G G) (fst G G)).left ≫ (inc ⊗ₘ inc).left =
      (inc ⊗ₘ inc).left ≫ (lift (snd A A) (fst A A)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [lift_map, comp_lift]
  obtain ⟨t₁, ht₁⟩ := r₁
  obtain ⟨t₂, ht₂⟩ := r₂
  exact ⟨gen_chartPull (chartPullLinComb P (inc ⊗ₘ inc).left _ _ _ inc.left (fun _ => e₁)) t₁ ht₁,
    gen_chartPull (chartPullLinComb P (inc ⊗ₘ inc).left _ _ _ inc.left (fun _ => e₂)) t₂ ht₂,
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
      (chartPullLinComb P _ _ _ _ (inc ⊗ₘ inc).left (fun _ => e₃)) sy⟩

end GlobalTheory.IdemLocus

namespace GlobalTheory.IdemLocus

theorem image_bundle_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G]
    [IsCommMonObj G] (P : LB (G2 A).left) (hP : P.IsLB) (inc : G ⟶ A) :
    LBIso ((P.pull (inc ⊗ₘ inc).left).pull (Pdiv.PullbackComparison.pφ₂ f G))
      ((P.pull (Pdiv.PullbackComparison.pφ₂ f A)).pull ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left) := by
  have hm : ((Over.pullback f).map inc).left ≫ Pdiv.PullbackComparison.pφ f A = Pdiv.PullbackComparison.pφ f G ≫ inc.left :=
    Pdiv.PullbackComparison.pullback_map_left_fst' f inc
  have key : Pdiv.PullbackComparison.pφ₂ f G ≫ (inc ⊗ₘ inc).left =
      ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left ≫ Pdiv.PullbackComparison.pφ₂ f A := by
    apply Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
    · have ht : (inc ⊗ₘ inc).left ≫ (fst A A).left = (fst G G).left ≫ inc.left := by
        rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
      have ht' : ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left ≫
          (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left =
          (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ ((Over.pullback f).map inc).left := by
        rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
      simp only [Category.assoc]
      rw [ht, reassoc_of% (Pdiv.PullbackComparison.pφ₂_fst f G), Pdiv.PullbackComparison.pφ₂_fst f A, reassoc_of% ht', hm]
    · have ht : (inc ⊗ₘ inc).left ≫ (snd A A).left = (snd G G).left ≫ inc.left := by
        rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
      have ht' : ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left ≫
          (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left =
          (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ ((Over.pullback f).map inc).left := by
        rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
      simp only [Category.assoc]
      rw [ht, reassoc_of% (Pdiv.PullbackComparison.pφ₂_snd f G), Pdiv.PullbackComparison.pφ₂_snd f A, reassoc_of% ht', hm]
  have e₁ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP (inc ⊗ₘ inc).left))
    (Pdiv.PullbackComparison.pφ₂ f G)
  have e₂ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP (Pdiv.PullbackComparison.pφ₂ f A)))
    ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left
  rw [key] at e₁
  exact LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm

end GlobalTheory.IdemLocus

namespace GlobalTheory.IdemLocus

theorem adj_pullback' {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] (A : Over S) [GrpObj A] [IsCommMonObj A]
    (Q : LB (G2 A).left) (bar : O → O) (act : O → (A ⟶ A)) (hQ : Q.IsLB) (hA : Adj A Q bar act) :
    Adj ((Over.pullback f).obj A) (Q.pull (Pdiv.PullbackComparison.pφ₂ f A)) bar (fun a => (Over.pullback f).map (act a)) := by
  have hw : Pdiv.PullbackComparison.pφ f A ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f := pullback.condition
  have hA' : Adj A (Q.pull (𝟙 _)) bar act := fun a => by
    have e₁ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hQ (𝟙 (G2 A).left)))
      (lift (fst A A ≫ act a) (snd A A)).left
    have e₂ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hQ (𝟙 (G2 A).left)))
      (lift (fst A A) (snd A A ≫ act (bar a))).left
    rw [Category.comp_id] at e₁ e₂
    exact LBIso.trans (pull_isLB (pull_isLB hQ _) _) (pull_isLB hQ _) (pull_isLB (pull_isLB hQ _) _) e₁
      (LBIso.trans (pull_isLB hQ _) (pull_isLB hQ _) (pull_isLB (pull_isLB hQ _) _) (hA a) e₂.symm)
  have key := ActUnr.adj_along hw act (fun a => (Over.pullback f).map (act a))
    (fun a => Pdiv.PullbackComparison.pullback_map_left_fst' f (act a)) Q (𝟙 _) bar hA'
  have hsq : ActUnr.sqMap hw ≫ 𝟙 _ = Pdiv.PullbackComparison.pφ₂ f A := by
    rw [Category.comp_id]
    apply Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
    · rw [ActUnr.sqMap_fst, Pdiv.PullbackComparison.pφ₂_fst]
    · rw [ActUnr.sqMap_snd, Pdiv.PullbackComparison.pφ₂_snd]
  rw [hsq] at key
  exact key

end GlobalTheory.IdemLocus

namespace GlobalTheory.IdemLocus

theorem exists_open_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (U : S'.Opens) (c : SiegPre h M (zetaAway M) (U.ι ≫ t)) (w : SiegPre h' M (zetaAway M) (U.ι ≫ t)) (actw : O → (w.A ⟶ w.A)), SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(U.toScheme, ⊤)) ∧ w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act U.ι ∧ ZRel e jl o κ c w actw ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)), IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g ∧ ZRel e jl o κ c' w' actw') → Set.range g.base ⊆ (U : Set S') := by
  intro h h' M d O _ bar e jl n o κ S' _ t z act hh hM hMo hd hMd hz hRA hAdj hee
  have hee' : act e ≫ act e = act e := by rw [← hRA.2.2.1, hee]
  haveI hae := hRA.1 e
  obtain ⟨G, _, _, inc, pr, hGs, hinc, hpr, hip, hpi⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image S' z.A (GlobalTheory.isSemiAbelian_of_isAbelianScheme z.A z.ab) (act e) (hRA.1 e)
      hee'
  haveI := hinc
  haveI := hpr
  have hGab : IsAbelianScheme G := GlobalTheory.T.isAbelianScheme_of_semiAbelian_hom_retract S' z.A G inc pr z.ab hGs hinc hpr hip
  let Pe : LB (G2 G).left := z.P.pull (inc ⊗ₘ inc).left
  have hPe : Pe.IsLB := pull_isLB z.isLB _
  obtain ⟨hr₁, hr₂, hsy⟩ := image_bundle_rig z.A G z.P inc z.rig₁ z.rig₂ z.symm
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G) := fun a => z.lev (jl a) ≫ pr
  have lev_add : ∀ a b, lev (a + b) = lev a * lev b := fun a b => by
    simp only [lev, map_add, z.lev_add, MonObj.mul_comp]
  have lev_tors : ∀ a, lev a ^ M = 1 := fun a => by
    simp only [lev, ← MonObj.pow_comp, z.lev_tors, MonObj.one_comp]

  have hM1 : 1 ≤ M := by omega
  let x₂ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ z.A) := fun a => z.lev (jl a) ≫ act e
  let y₂ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ z.A) := fun a => z.lev (jl a)
  let y₃ : (Fin h' ⊕ Fin h' → ℤ) → (𝟙_ (Over S') ⟶ z.A) :=
    fun a => (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod
  have hy₃ : ∀ a, y₃ a = ∏ k, z.lev (jl (κ k a)) ≫ act (o k) := fun a => List.prod_ofFn
  obtain ⟨U₁, hU₁, hT₁⟩ := GlobalTheory.T.natCast_unit_locus_open S' d
  obtain ⟨U₂, hU₂, hT₂⟩ := GlobalTheory.T.additive_torsion_families_equal_locus_open h M S' t z.A z.ab hM1 x₂ y₂
    (fun a b => by simp only [x₂, map_add, z.lev_add, MonObj.mul_comp])
    (fun a b => by simp only [y₂, map_add, z.lev_add])
    (fun a => by simp only [x₂, ← MonObj.pow_comp, z.lev_tors, MonObj.one_comp])
    (fun a => by simp only [y₂, z.lev_tors])
  obtain ⟨U₃, hU₃, hT₃⟩ := GlobalTheory.T.additive_torsion_families_equal_locus_open h' M S' t z.A z.ab hM1 z.lev y₃ z.lev_add
    (fun a b => by
      haveI := fun k => hRA.1 (o k)
      simp only [hy₃, map_add, z.lev_add, MonObj.mul_comp, Finset.prod_mul_distrib])
    z.lev_tors
    (fun a => by
      haveI := fun k => hRA.1 (o k)
      simp only [hy₃, ← Finset.prod_pow, ← MonObj.pow_comp, z.lev_tors, MonObj.one_comp, Finset.prod_const_one])
  obtain ⟨U₄, hU₄, hT₄⟩ := GlobalTheory.T.isOpen_symplecticLevel_locus h M S' t G Pe lev hGab hPe hr₁ hr₂ hsy hM hMo lev_add lev_tors
  obtain ⟨U₅, hU₅, hT₅⟩ := GlobalTheory.T.diagonal_restriction_relAmple_locus_open S' G Pe hGab hPe
  obtain ⟨U₆, hU₆, hT₆⟩ := GlobalTheory.T.exists_open_locus_kernel_killed_symmetric_bundle d S' G Pe hGab hPe hr₁ hr₂ hsy
  let U : S'.Opens := U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄ ⊓ U₅ ⊓ U₆
  have l₁ : U ≤ U₁ := inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  have l₂ : U ≤ U₂ := inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have l₃ : U ≤ U₃ := inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have l₄ : U ≤ U₄ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₅ : U ≤ U₅ := inf_le_left.trans inf_le_right
  have l₆ : U ≤ U₆ := inf_le_right
  have pbG := Pdiv.PullbackComparison.isGrpPullback U.ι G
  have hS := hU₄ U l₄
  let c : SiegPre h M (zetaAway M) (U.ι ≫ t) :=
    { A := (Over.pullback U.ι).obj G
      ab := GlobalTheory.isAbelianScheme_pullback_obj U.ι G hGab
      P := Pe.pull (Pdiv.PullbackComparison.pφ₂ U.ι G)
      isLB := pull_isLB hPe _
      rig₁ := by
        obtain ⟨t₁, ht₁⟩ := hr₁
        exact gen_chartPull (chartPullLinComb Pe _ _ _ _ (Pdiv.PullbackComparison.pφ U.ι G)
          (fun _ => Pdiv.PullbackComparison.lift_one_id U.ι G)) t₁ ht₁
      rig₂ := by
        obtain ⟨t₂, ht₂⟩ := hr₂
        exact gen_chartPull (chartPullLinComb Pe _ _ _ _ (Pdiv.PullbackComparison.pφ U.ι G)
          (fun _ => Pdiv.PullbackComparison.lift_id_one U.ι G)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Pe _ _ rfl)
        (chartPullLinComb Pe _ _ _ _ (Pdiv.PullbackComparison.pφ₂ U.ι G) (fun _ => Pdiv.PullbackComparison.lift_swap U.ι G)) hsy
      lev := fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι G) (lev a)
      lev_add := hS.1
      lev_tors := hS.2.1
      geom := hS.2.2 }
  let w : SiegPre h' M (zetaAway M) (U.ι ≫ t) := GlobalTheory.LowChart.siegPull z U.ι (U.ι ≫ t) rfl
  let actw : O → (w.A ⟶ w.A) := fun a => (Over.pullback U.ι).map (act a)
  refine ⟨U, c, w, actw, ⟨hU₅ U l₅, hU₆ U l₆⟩, hU₁ U l₁, GlobalTheory.LowChart.principal_siegPull z U.ι _ rfl hz,
    ActUnr.isRAct_pullback U.ι z.A act hRA, adj_pullback' U.ι z.A z.P bar act z.isLB hAdj, ?_, ?_, ?_⟩

  · exact ⟨Pdiv.PullbackComparison.pφ U.ι z.A, Pdiv.PullbackComparison.pφ₂ U.ι z.A, Pdiv.PullbackComparison.isGrpPullback U.ι z.A,
      Pdiv.PullbackComparison.isSquare U.ι z.A, Pdiv.PullbackComparison.gen_refl _ (pull_isLB z.isLB _),
      fun a => GlobalTheory.SiegelPull.secPull_left (Pdiv.PullbackComparison.isGrpPullback U.ι z.A) (z.lev a), fun a => Pdiv.PullbackComparison.pullback_map_left_fst' U.ι (act a)⟩
  · refine ⟨(Over.pullback U.ι).map inc, (Over.pullback U.ι).map pr,
      (by exact (inferInstance : IsMonHom ((Over.pullback U.ι).map inc))),
      (by exact (inferInstance : IsMonHom ((Over.pullback U.ι).map pr))), ?_, ?_, ?_, ?_, ?_⟩
    · exact (CategoryTheory.Functor.map_comp _ _ _).symm.trans ((congrArg _ hip).trans (CategoryTheory.Functor.map_id _ _))
    · exact (CategoryTheory.Functor.map_comp _ _ _).symm.trans (congrArg _ hpi)
    · exact image_bundle_pull U.ι z.A G z.P z.isLB inc
    · intro a
      show GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι G) (z.lev (jl a) ≫ pr) ≫ (Over.pullback U.ι).map inc =
        GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι z.A) (z.lev (jl a))
      rw [secPull_map, Category.assoc, hpi]
      exact secPull_congr _ (hU₂ U l₂ a)
    · intro a
      show GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι z.A) (z.lev a) = _
      rw [secPull_congr _ (hU₃ U l₃ a), secPull_prod]
      congr 1
      apply congrArg List.ofFn
      funext k
      show _ = GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι G) (z.lev (jl (κ k a)) ≫ pr) ≫ (Over.pullback U.ι).map inc ≫
        (Over.pullback U.ι).map (act (o k))
      rw [← Category.assoc, secPull_map, secPull_map]
      simp only [Category.assoc, reassoc_of% hpi]
      apply secPull_congr
      have := hU₂ U l₂ (κ k a)
      simp only [x₂, y₂, Over.comp_left] at this ⊢
      rw [reassoc_of% this]
  · intro T g c' hdT hker ⟨w', actw', hpb, hzr⟩
    obtain ⟨hl₂, hl₃⟩ := GlobalTheory.T.level_sections_formulas_of_idempotent_image_pullback h h' M O e jl n o κ S' T t z act g c' w' actw' hpb hzr
    obtain ⟨inc', pr', hinc', hpr', hip', hpi', hP', hl', -⟩ := hzr
    obtain ⟨ψ, ψ₂, hψ, hsq, hw', hlw, hact⟩ := hpb
    obtain ⟨φ, φ₂, hφ, hsqφ, hiφ, hiφ₂⟩ := GlobalTheory.T.idempotent_endomorphism_image_commutes_base_change S' T g z.A G inc pr (act e) w'.A c'.A inc' pr' (actw' e)
      ψ ψ₂ hinc hpr hip hpi hinc' hpr' hip' hpi' hψ hsq (hact e)
    have hcP : LBIso c'.P (Pe.pull φ₂) := by
      have e₁ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp hw' (inc' ⊗ₘ inc').left
      rw [hiφ₂] at e₁
      have e₂ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl hPe) φ₂
      exact LBIso.trans c'.isLB (pull_isLB w'.isLB _) (pull_isLB hPe _) hP'
        (LBIso.trans (pull_isLB w'.isLB _) (pull_isLB z.isLB _) (pull_isLB hPe _) e₁ e₂.symm)
    have hcl : ∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left := fun a => by
      have h₀ : (c'.lev a).left ≫ φ ≫ inc.left = g ≫ (z.lev (jl a)).left := by
        rw [← hiφ, ← Category.assoc, ← Over.comp_left, hl' a, hlw]
      calc (c'.lev a).left ≫ φ = (c'.lev a).left ≫ φ ≫ (inc ≫ pr).left := by
            rw [hip, Over.id_left, Category.comp_id]
        _ = ((c'.lev a).left ≫ φ ≫ inc.left) ≫ pr.left := by rw [Over.comp_left]; simp only [Category.assoc]
        _ = g ≫ (lev a).left := by rw [h₀]; simp only [lev, Over.comp_left, Category.assoc]
    intro x hx
    simp only [U, TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]
    exact ⟨⟨⟨⟨⟨hT₁ T g hdT hx, hT₂ T g hl₂ hx⟩, hT₃ T g hl₃ hx⟩, hT₄ T g c' φ φ₂ hφ hsqφ hcP hcl hx⟩,
      hT₅ T g c'.A φ φ₂ c'.P hφ hsqφ c'.isLB hcP hker.1 hx⟩,
      hT₆ T g c'.A φ φ₂ c'.P hφ hsqφ c'.isLB hcP hdT hker.1 hker.2 hx⟩

end GlobalTheory.IdemLocus
