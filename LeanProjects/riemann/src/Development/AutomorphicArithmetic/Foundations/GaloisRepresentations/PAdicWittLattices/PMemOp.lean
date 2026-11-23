import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem cos_bij {G : Type} [Group G] (K V U : Subgroup G) (hVK : V ≤ K) (hUV : U ≤ V) :
    Function.Bijective (fun p : (K ⧸ V.subgroupOf K) × (V ⧸ U.subgroupOf V) =>
      (((⟨(p.1.out : G) * (p.2.out : G), K.mul_mem p.1.out.2 (hVK p.2.out.2)⟩ : K)) : K ⧸ U.subgroupOf K)) := by
  constructor
  · rintro ⟨c, y⟩ ⟨c', y'⟩ h
    have h1 : ((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G)) ∈ U := by
      have := QuotientGroup.eq.1 h
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((c.out)⁻¹ * c'.out : K) : G) =
          (y.out : G) * (((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G))) * (y'.out : G)⁻¹ := by
        push_cast; group
      rw [e]
      exact V.mul_mem (V.mul_mem y.out.2 (hUV h1)) (V.inv_mem y'.out.2)
    subst hc
    have hy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((y.out)⁻¹ * y'.out : V) : G) =
          ((c.out : G) * (y.out : G))⁻¹ * ((c.out : G) * (y'.out : G)) := by
        push_cast; group
      rw [e]; exact h1
    rw [hy]
  · intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf K) a
      have hvV : ((v : K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
      let b : V := ⟨((v : K) : G)⁻¹, V.inv_mem hvV⟩
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf V) b
      have hwU : ((w : V) : G) ∈ U := Subgroup.mem_subgroupOf.1 w.2
      refine ⟨((a : K ⧸ V.subgroupOf K), (b : V ⧸ U.subgroupOf V)), ?_⟩
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((((⟨(((a : K ⧸ V.subgroupOf K).out : K) : G) * (((b : V ⧸ U.subgroupOf V).out : V) : G),
          K.mul_mem (a : K ⧸ V.subgroupOf K).out.2 (hVK (b : V ⧸ U.subgroupOf V).out.2)⟩ : K))⁻¹ * a : K) : G) =
          ((w : V) : G)⁻¹ := by
        simp only [hv, hw, b]
        push_cast
        group
      rw [e]; exact U.inv_mem hwU

theorem UpperTheory.Gal.G3.pMemOp :
    KNBasic → PlInv.{u} → HopDeep.{u} → HopEx.{u} → TwMem.{u} → SumFn.{u} → MemOp.{u} := by
  intro hKN _ hHD hHE hTw hSum p _ D G L R _ _ gb k T N J g j F _ _ Θ hΘ f hf
  classical
  have hnorm : ∀ c ∈ L.KN 1, ∀ u ∈ L.KN (g j).M.1, c * u * c⁻¹ ∈ L.KN (g j).M.1 :=
    fun c hc => (hKN p D G L (g j).M.1).1 c hc
  have hfin : ∀ (M' : ℕ) (K' : Subgroup G.GAf), 0 < M' → K' ≤ L.KN 1 → Finite (K' ⧸ (L.KN M').subgroupOf K') := by
    intro M' K' hM' hK'
    have h1 : (L.KN M').relIndex (L.KN 1) ≠ 0 := (hKN p D G L 1).2.2 M' one_pos hM'
    have h2 : (L.KN M').relIndex K' ≠ 0 := fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right hK' h0)
    haveI : ((L.KN M').subgroupOf K').FiniteIndex := ⟨h2⟩
    infer_instance
  have hMpos : 0 < (g j).M.1 := by have := (g j).M.2.1; omega
  have hNpos : 0 < N.1 := by have := N.2.1; omega
  have hUV : L.KN (g j).M.1 ≤ L.KN N.1 := UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd
  have hV1 : L.KN N.1 ≤ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _)
  haveI := hfin _ (g j).K hMpos (g j).le_one
  haveI := hfin _ (g j).K hNpos (g j).le_one
  haveI := hfin (g j).M.1 (L.KN N.1) hMpos hV1
  letI : Fintype ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) := Fintype.ofFinite _
  letI : Fintype ((g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) := Fintype.ofFinite _
  letI : Fintype (L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)) := Fintype.ofFinite _
  have hadm : ∀ c ∈ (g j).K, T.X.admitted (T.lev (g j).M) (T.lev N) ((g j).h * c) := fun c hc =>
    ⟨(T.Δ_eq _).2 ((g j).int.mul (UpperTheory.Gal.Int.Geo.integ_of_mem ((g j).le_one hc))), fun u hu => by
      rw [T.K_eq] at hu ⊢
      exact (g j).adm c hc u hu⟩
  have hmem : ∀ c ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, ∀ y,
      (g j).h * (c * u) * y ∈ L.KN N.1 ↔ (g j).h * c * y ∈ L.KN N.1 := by
    intro c hc u hu y
    have e : (g j).h * (c * u) * y = ((g j).h * c * u * ((g j).h * c)⁻¹) * ((g j).h * c * y) := by group
    rw [e]
    exact Subgroup.mul_mem_cancel_left _ ((g j).adm c hc u hu)
  have hpl : ∀ c ∈ (g j).K, ∀ u ∈ L.KN (g j).M.1, ∀ x,
      T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * (c * u)) x = T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * c) x := by
    intro c hc u hu x
    have e : (g j).h * (c * u) = ((g j).h * c * u * ((g j).h * c)⁻¹) * ((g j).h * c) := by group
    rw [e]
    exact T.X.pl_left Θ (hadm c hc) (by rw [T.K_eq]; exact (g j).adm c hc u hu) x
  have hS := hSum T.X Θ (T.lev (g j).M) (T.lev N) ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K)
    (fun a => (g j).h * (a.out : G.GAf)) (fun a => hadm _ a.out.2) f (fun y => by rw [hf y, T.K_eq])
  have hinv : ∀ k ∈ T.X.K (T.lev N), ∀ y, f (k * y) = f y := by
    intro k₀ hk₀ y
    rw [T.K_eq] at hk₀
    have hk₀K : k₀ ∈ (g j).K := (g j).le hk₀
    let σ : ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) → ((g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K) :=
      fun a => ((a.out * ⟨k₀, hk₀K⟩ : (g j).K) : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K)
    have hσ : Function.Injective σ := by
      intro a b hab
      have h1 := QuotientGroup.eq.1 hab
      rw [Subgroup.mem_subgroupOf] at h1
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((a.out)⁻¹ * b.out : (g j).K) : G.GAf) = k₀ *
          ((((a.out * ⟨k₀, hk₀K⟩ : (g j).K))⁻¹ * (b.out * ⟨k₀, hk₀K⟩) : (g j).K) : G.GAf) * k₀⁻¹ := by
        push_cast; group
      rw [e]
      exact hnorm k₀ (hV1 hk₀) _ h1
    have hσb : Function.Bijective σ := Finite.injective_iff_bijective.1 hσ
    have hcard : Nat.card {a : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (a.out : G.GAf) * (k₀ * y) ∈ L.KN N.1} =
        Nat.card {a : (g j).K ⧸ (L.KN (g j).M.1).subgroupOf (g j).K // (g j).h * (a.out : G.GAf) * y ∈ L.KN N.1} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective σ hσb) fun a => ?_)
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (g j).K) (a.out * ⟨k₀, hk₀K⟩)
      have hwU : ((w : (g j).K) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
      have e : (σ a).out = a.out * ⟨k₀, hk₀K⟩ * w := hw
      have e2 : (((Equiv.ofBijective σ hσb) a).out : G.GAf) = (a.out : G.GAf) * k₀ * ((w : (g j).K) : G.GAf) := by
        simp [e]
      rw [e2, hmem _ ((g j).K.mul_mem a.out.2 hk₀K) _ hwU y]
      simp only [_root_.mul_assoc]
    rw [hf, hf, hcard]
  have hIsFn := hS.2.1 hinv
  have hle : T.X.K (T.lev (g j).M) ≤ T.X.K (T.lev N) := by
    rw [T.K_eq, T.K_eq]; exact hUV
  refine ⟨hIsFn, fun tr htr => ?_⟩
  refine (hHE T.X Θ hΘ (T.lev N) f hIsFn).2 _ ((hHD T.X Θ hΘ (T.lev N) f hIsFn).2 _ (T.lev (g j).M) hle hS.1 fun x => ?_)
  rw [← hS.2.2 x]
  have hU' : ∀ y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1), ((y.out : L.KN N.1) : G.GAf) ∈ T.X.K (T.lev N) := by
    intro y; rw [T.K_eq]; exact y.out.2
  have hex : ∀ k ∈ T.X.K (T.lev N), ∃! y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1),
      k * ((y.out : L.KN N.1) : G.GAf)⁻¹ ∈ T.X.K (T.lev (g j).M) := by
    intro k hk
    rw [T.K_eq] at hk
    simp only [T.K_eq]
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (L.KN N.1)) ⟨k, hk⟩
    have hwU : ((w : L.KN N.1) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
    refine ⟨((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)), ?_, fun y' hy' => ?_⟩
    · have e : k * ((((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)).out : L.KN N.1) : G.GAf)⁻¹ =
          k * ((w : L.KN N.1) : G.GAf)⁻¹ * k⁻¹ := by
        rw [hw]; push_cast; group
      show k * ((((⟨k, hk⟩ : L.KN N.1) : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)).out : L.KN N.1) : G.GAf)⁻¹ ∈ _
      rw [e]
      exact hnorm k (hV1 hk) _ ((L.KN (g j).M.1).inv_mem hwU)
    · rw [← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((y'.out⁻¹ * ⟨k, hk⟩ : L.KN N.1) : G.GAf) =
          ((y'.out : L.KN N.1) : G.GAf)⁻¹ * (k * ((y'.out : L.KN N.1) : G.GAf)⁻¹) * ((y'.out : L.KN N.1) : G.GAf)⁻¹⁻¹ := by
        push_cast; group
      rw [e]
      exact hnorm _ (hV1 ((L.KN N.1).inv_mem y'.out.2)) _ hy'
  have hTw' := hTw T.X Θ (T.lev (g j).M) (T.lev (g j).M) (T.lev N) (T.X.isAdmissibleIntegralBasisChange_one hle) le_rfl
    (fun k hk u hu => by
      rw [T.K_eq] at hk hu ⊢
      exact hnorm k (hV1 hk) u hu)
    ((g j).K ⧸ (L.KN N.1).subgroupOf (g j).K) (L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1))
    (fun c => (g j).h * (c.out : G.GAf)) (fun c => hadm _ c.out.2)
    (fun y => ((y.out : L.KN N.1) : G.GAf)) hU' hex ((T.tower N g).comm j) tr htr x
  refine Eq.trans hTw' ?_
  refine (Fintype.sum_prod_type' (fun (c : (g j).K ⧸ (L.KN N.1).subgroupOf (g j).K)
    (y : L.KN N.1 ⧸ (L.KN (g j).M.1).subgroupOf (L.KN N.1)) =>
      T.X.pl Θ (T.lev (g j).M) (T.lev N) ((g j).h * (c.out : G.GAf) * ((y.out : L.KN N.1) : G.GAf)) x)).symm.trans ?_
  refine Fintype.sum_bijective _ (cos_bij (g j).K (L.KN N.1) (L.KN (g j).M.1) (g j).le hUV) _ _ fun q => ?_
  obtain ⟨c, y⟩ := q
  have hcy : (c.out : G.GAf) * ((y.out : L.KN N.1) : G.GAf) ∈ (g j).K := (g j).K.mul_mem c.out.2 ((g j).le y.out.2)
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul ((L.KN (g j).M.1).subgroupOf (g j).K) ⟨_, hcy⟩
  have hwU : ((w : (g j).K) : G.GAf) ∈ L.KN (g j).M.1 := Subgroup.mem_subgroupOf.1 w.2
  dsimp only
  rw [hw]
  push_cast
  rw [hpl _ hcy _ hwU x, _root_.mul_assoc]
