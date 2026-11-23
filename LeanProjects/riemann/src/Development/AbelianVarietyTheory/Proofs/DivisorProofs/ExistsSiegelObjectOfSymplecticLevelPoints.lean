import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSiegPre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegelLevelPull

theorem exists_siegPre_of_points : ∀ (n : ℕ) (hn : 3 ≤ n) (V V₁ : Type) [CommRing V] [CommRing V₁] [IsLocalRing V₁] [IsNoetherianRing V₁] (f₁ : V →+* V₁) (b : cycAway n →+* V) (PB : PolAV (Sp V)) (lev : (Fin PB.g ⊕ Fin PB.g → ℤ) → (Over.mk (spMap f₁) ⟶ PB.A)) (r : ℕ) (d₀ : Fin r → (Over.mk (spMap f₁) ⟶ PB.A)) (c : Fin r → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ n = 1) → (∀ x y, Out.WeilIs PB.A PB.L n (lev x) (lev y) (unitOn (Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit ^ omegaStd x y))) → (∀ i, d₀ i ^ n = toUnit _ ≫ c i) → ∃ (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c i).left := by
  intro n hn V V₁ _ _ _ _ f₁ b PB lev r d₀ c hadd htors hweil hd
  have hn0 : n ≠ 0 := by omega
  haveI := PB.isAb.comm
  let P₁ : PolAV (Sp V₁) := GlobalTheory.StrictPull.polPull PB (spMap f₁)
  haveI : IsCommMonObj P₁.A := P₁.isAb.comm
  have hpb : IsGrpPullback P₁.A PB.A (spMap f₁) (pullback.fst PB.A.hom (spMap f₁)) :=
    isGrpPullback_pullback PB.A (spMap f₁)
  obtain ⟨κ, hκ⟩ := GlobalTheory.UnifPoint.exists_pointEquiv hpb
  have hk : ∀ x, (κ.symm x).left ≫ pullback.fst PB.A.hom (spMap f₁) = x.left := fun x => by
    rw [← hκ, κ.apply_symm_apply]
  let ze : V₁ˣ := Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit
  let lev₁ : (Fin PB.g ⊕ Fin PB.g → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ P₁.A) := fun x => κ.symm (lev x)
  have hL₁ : LBIso P₁.L (PB.L.pull (pullback.fst PB.A.hom (spMap f₁))) :=
    GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB PB.isLB _)
  have hw : ∀ x y, WeilIs P₁.A P₁.L n (lev₁ x) (lev₁ y) (unitOn (ze ^ omegaStd x y)) := fun x y =>
    (GlobalTheory.weilIs_grpPullback_of_comm _ _ PB.A P₁.A (spMap f₁) _ PB.L P₁.L PB.isLB P₁.isLB hpb hL₁ _ n _ _
      (pushPt hpb.1.w (lev₁ x)) (pushPt hpb.1.w (lev₁ y)) _ rfl rfl).2
      (GlobalTheory.UnifPoint.weilIs_congr (Category.id_comp _).symm (hk _).symm (hk _).symm (hweil x y))
  have hadd₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y => by
    simp only [lev₁, hadd, map_mul]
  have htors₁ : ∀ x, lev₁ x ^ n = 1 := fun x => by
    simp only [lev₁, ← map_pow, htors, map_one]
  have hu : IsUnit (n : V₁) := by simpa using (GlobalTheory.SiegelTor.isUnit_natCast hn0).map (f₁.comp b)
  have hze : (ze : V₁) = (f₁.comp b) (zetaAway n) := by simp [ze]
  have hprim : ∀ (k : Type) [Field k] (gk : V₁ →+* k), IsPrimitiveRoot (gk ze) n := fun k _ gk => by
    rw [hze]; exact GlobalTheory.SiegelTor.isPrimitiveRoot_map hn0 (gk.comp (f₁.comp b))
  haveI : IsMonHom (Iso.refl P₁.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have hid : IsGrpPullback P₁.A P₁.A (spMap (RingHom.id V₁)) (𝟙 _) :=
    (isGrpPullback_of_iso (Iso.refl P₁.A)).congr (by simp [spMap]) rfl
  obtain ⟨s, ψ, hψ, hs, hsP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre V₁ V₁ P₁ (RingHom.id V₁) P₁ (𝟙 _) hid
    (GlobalTheory.lbIso_pull_id P₁.isLB).symm rfl (cycAway n) (f₁.comp b) PB.g n (zetaAway n) ze lev₁ rfl hu hze hprim
    hadd₁ htors₁ hw

  haveI := hψ
  have hLamB : (abelian₂ PB.A PB.L).IsLB := DVR.linComb_isLB _ PB.isLB _ _
  have hLam₁ : (abelian₂ P₁.A P₁.L).IsLB := DVR.linComb_isLB _ P₁.isLB _ _
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap f₁) PB.A P₁.A _ hpb
  have e₁ : LBIso (abelian₂ P₁.A P₁.L) ((abelian₂ PB.A PB.L).pull (β₂ ≫ 𝟙 _)) :=
    hlam PB.L P₁.L _ (abelian₂ PB.A PB.L) (𝟙 _) PB.isLB P₁.isLB hLamB hL₁ (GlobalTheory.lbIso_pull_id hLamB).symm
  rw [Category.comp_id] at e₁
  let κ₂ := (lift (fst s.A s.A ≫ ψ.hom) (snd s.A s.A ≫ ψ.hom)).left
  have e₂ : LBIso ((abelian₂ P₁.A P₁.L).pull κ₂) ((abelian₂ PB.A PB.L).pull (κ₂ ≫ β₂)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl) (chartPullSame (abelian₂ PB.A PB.L) _ (fun _ => β₂) _ κ₂ fun _ => rfl) e₁
  let d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A) := fun i => κ.symm (d₀ i) ≫ ψ.inv
  have hpow : ∀ (x : 𝟙_ (Over (Sp V₁)) ⟶ P₁.A) (m : ℕ), ((x ≫ ψ.inv) ^ m) ≫ ψ.hom = x ^ m := fun x m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ m ih => rw [pow_succ, MonObj.mul_comp, ih, Category.assoc, Iso.inv_hom_id, Category.comp_id, pow_succ]
  refine ⟨s, ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁), κ₂ ≫ β₂, d, hs,
    ((isGrpPullback_of_iso ψ).comp hpb).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩,
    LBIso.trans s.isLB (pull_isLB hLam₁ _) (pull_isLB hLamB _) hsP e₂, fun i => ?_⟩
  · rw [Category.assoc, hsq.1]
    have e : κ₂ ≫ (fst P₁.A P₁.A).left = (fst s.A s.A).left ≫ ψ.hom.left := by
      simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_fst]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
  · rw [Category.assoc, hsq.2]
    have e : κ₂ ≫ (snd P₁.A P₁.A).left = (snd s.A s.A).left ≫ ψ.hom.left := by
      simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_snd]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
  · have h1 : (d i ^ n).left ≫ ψ.hom.left = (κ.symm (d₀ i) ^ n).left := by
      rw [← Over.comp_left, hpow]
    have hT : (toUnit (Over.mk (spMap f₁))).left = spMap f₁ := by
      simpa using Over.w (toUnit (Over.mk (spMap f₁)))
    calc (d i ^ n).left ≫ ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁)
        = ((d i ^ n).left ≫ ψ.hom.left) ≫ pullback.fst PB.A.hom (spMap f₁) := (Category.assoc _ _ _).symm
      _ = (κ.symm (d₀ i) ^ n).left ≫ pullback.fst PB.A.hom (spMap f₁) := by rw [h1]
      _ = (d₀ i ^ n).left := by rw [← map_pow, hk]
      _ = spMap f₁ ≫ (c i).left := by rw [hd, Over.comp_left, hT]

end GlobalTheory.SiegelLevelPull
