import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTwGal :
    TwSplit → TwGal := by
  intro hS B G _ X m j b hnorm
  classical
  haveI hN : ((X.K m).subgroupOf (X.K j)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    push_cast
    exact hnorm g g.2 n hn⟩
  haveI : Finite (X.K j ⧸ (X.K m).subgroupOf (X.K j)) := Nat.finite_of_card_ne_zero (X.idx m j)
  have admr : ∀ c : X.K j ⧸ (X.K m).subgroupOf (X.K j), X.admitted m m ((c.out : X.K j) : G)⁻¹ := fun c =>
    ⟨X.K_le j _ (inv_mem c.out.2), fun u hu => hnorm _ (inv_mem c.out.2) u hu⟩
  have uniq : ∀ k ∈ X.K j, ∃! c : X.K j ⧸ (X.K m).subgroupOf (X.K j),
      k * (((c.out : X.K j) : G))⁻¹⁻¹ ∈ X.K m := by
    intro k hk
    refine ⟨QuotientGroup.mk ⟨k⁻¹, inv_mem hk⟩, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul ((X.K m).subgroupOf (X.K j)) (⟨k⁻¹, inv_mem hk⟩ : X.K j)
      simp only [inv_inv]
      rw [hu]
      have hu' : ((u : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp u.2
      simpa [mul_assoc] using hu'
    · intro c hc
      simp only [inv_inv] at hc
      rw [← QuotientGroup.out_eq' c, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_inv_rev] using inv_mem hc
  have trc : ∀ (g1 g2 : G) (e : g1 = g2) (p1 : X.admitted m m g1) (p2 : X.admitted m m g2),
      X.tr m m g1 p1.1 p1.2 = X.tr m m g2 p2.1 p2.2 := by
    intro g1 g2 e p1 p2
    subst e
    rfl
  have tl : ∀ (g k : G) (hg : X.admitted m m g) (hk : k ∈ X.K m) (hkg : X.admitted m m (k * g)),
      X.tr m m (k * g) hkg.1 hkg.2 = X.tr m m g hg.1 hg.2 := by
    intro g k hg hk hkg
    rw [← X.tr_mul m m m g k hg.1 hg.2 (X.K_le m k hk) (X.tower_admissible_self hk).2 hkg.1 hkg.2,
      X.tr_self m k _ _ hk, Category.comp_id]
  refine ⟨X.K j ⧸ (X.K m).subgroupOf (X.K j), inferInstance, inferInstance,
    fun c => ((c.out : X.K j) : G)⁻¹, admr, fun c => inv_mem c.out.2, uniq, ?_⟩
  unfold GlobalTheory.GalV.IsGalois
  refine ⟨X.fin m j b.1 b.2, X.etale m j b.1 b.2, X.onto m j b.1 b.2, ?_, ?_,
    hS X m m j b b le_rfl hnorm _ _ admr (fun c => inv_mem c.out.2) uniq⟩
  · have h1 : ((1 : X.K j ⧸ (X.K m).subgroupOf (X.K j)).out : G) ∈ X.K m :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (QuotientGroup.out_eq' 1))
    exact X.tr_self m _ _ _ (inv_mem h1)
  · intro g g'
    set w : X.K j := ((g.out : X.K j) * g'.out)⁻¹ * (g * g').out with hwdef
    have hw : w ∈ (X.K m).subgroupOf (X.K j) := by
      rw [hwdef, ← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
        QuotientGroup.out_eq']
    have hw' : ((w : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp hw
    have e : (((g * g').out : X.K j) : G)⁻¹ =
        ((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) := by
      simp only [hwdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hA : X.admitted m m ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) :=
      Tower.admitted.mul (admr g) (admr g')
    have hB : X.admitted m m (((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹)) :=
      Tower.admitted.mul hA (X.tower_admissible_self (inv_mem hw'))
    exact ((trc _ _ e (admr (g * g')) hB).trans (tl _ _ hA (inv_mem hw') hB)).trans
      (X.tr_mul m m m _ _ (admr g).1 (admr g).2 (admr g').1 (admr g').2 hA.1 hA.2).symm
