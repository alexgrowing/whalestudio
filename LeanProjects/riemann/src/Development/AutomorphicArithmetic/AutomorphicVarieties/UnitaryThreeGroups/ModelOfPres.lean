import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsLocPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsTorusTwistEqLocalPointOfWeightedPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDualNumberPointOfPointDerivationVanishing
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsBasePointDerivationOfWeightHomogeneous
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsPointDerivationEmbEntryEqSmulMatEntry
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsSpanEntMonApproxOfMemWtPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsOriginAndChartOfIsLocPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsSurjectionUnivNormCondKerSpanNEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsEqnsOfWeightedGenerators
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.IsWRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem mop_rename_mem {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ τ : Type} [Finite σ]
    (u : σ → τ) (wt : τ → X) (ws : σ → X) (h : ∀ s, wt (u s) = ws s) {j : X} {g : MvPowerSeries σ O}
    (hg : g ∈ wtPart O ws j) : MvPowerSeries.rename u g ∈ wtPart O wt j := fun n hn => by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun d hd => hg d fun hj => hn ?_
  have hd' : Finsupp.mapDomain u d = n := by simpa using hd
  rw [← hd', ← hj, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul])]
  simp [h]

private theorem mop_homog {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ : Type} [Fintype σ]
    (wt : σ → X) {κ : Type} [Finite κ] (g : κ → MvPowerSeries σ O) (c : κ → X)
    (hg : ∀ i, g i ∈ wtPart O wt (c i)) : IsHomog O wt (Ideal.span (Set.range g)) := by
  have hp : ∀ i, g i ∈ (WPres.free O wt).part (c i) := fun i => ⟨g i, hg i, rfl⟩
  exact (homog_span O _ X (WPres.free O wt) κ (fun i => ⟨g i, (WPres.free O wt).part_le_A (hp i)⟩) c hp).1

private theorem mop_cover {O Bl B S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing Bl] [Algebra O Bl] [CommRing B] [Algebra O B] [CommRing S]
    [Algebra O S] [Nontrivial S] (WB : WPres O ℤ Bl) (i : Bl →ₐ[O] B) (W : WPres O ℤ B) {τ κ κ' : Type}
    (e : WB.σ ⊕ τ ≃ W.σ) (f : κ → MvPowerSeries W.σ O) (wf : κ → ℤ) (hrel : IsRelPres WB i W e f wf)
    (p : B →ₐ[O] S) (hp : Function.Surjective p) (n : κ' → B) (wn : κ' → ℤ) (hn : ∀ k, n k ∈ W.part (wn k))
    (hk : RingHom.ker p = Ideal.span (Set.range n)) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (WA : WPres O ℤ R) (ε : WB.σ ⊕ τ ≃ WA.σ)
      (qh : R →ₐ[O] S) (g : κ ⊕ κ' → WA.A),
      (∀ s, WA.wt (ε s) = W.wt (e s)) ∧ (∀ s, qh (WA.z (ε s)) = p (W.z (e s))) ∧
      RingHom.ker WA.π = (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => ε (.inl s)) ∧
      Function.Surjective qh ∧ (∀ k, g k ∈ WA.gr (Sum.elim wf wn k)) ∧
      RingHom.ker qh = Ideal.span (Set.range fun k => (g k : R)) ∧
      ∀ j, ∀ y ∈ W.part j, ∃ y' ∈ WA.part j, qh y' = p y := by
  obtain ⟨he1, -, hf, hker⟩ := hrel
  set J : Ideal (MvPowerSeries W.σ O) := (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) with hJ
  have hJh : IsHomog O W.wt J := by
    obtain ⟨k, f0, c0, hf0, h0⟩ := ker_gen O ℤ WB.σ WB.wt _ WB.homog
    rw [hJ, h0, Ideal.map_span, ← Set.range_comp]
    exact mop_homog W.wt _ c0 fun t => mop_rename_mem _ W.wt WB.wt he1 (hf0 t)
  have hle : ∀ F ∈ J, (p.comp W.π) F = 0 := fun F hF => by
    have : W.π F = 0 := (hker ▸ Ideal.mem_sup_left hF : F ∈ RingHom.ker W.π)
    rw [AlgHom.comp_apply, this, map_zero]
  let qh : (MvPowerSeries W.σ O ⧸ J) →ₐ[O] S := Ideal.Quotient.liftₐ J (p.comp W.π) hle
  have hqh : ∀ F, qh (Ideal.Quotient.mk J F) = p (W.π F) := fun _ => rfl
  haveI : Nontrivial (MvPowerSeries W.σ O ⧸ J) := qh.toRingHom.domain_nontrivial
  haveI := co_mvps O O W.σ
  haveI : IsCO O (MvPowerSeries W.σ O ⧸ J) :=
    co_quot O _ _ (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hkm : RingHom.ker (Ideal.Quotient.mkₐ O J) = J := Ideal.Quotient.mkₐ_ker O J
  let WA : WPres O ℤ (MvPowerSeries W.σ O ⧸ J) :=
    { σ := W.σ, wt := W.wt, π := Ideal.Quotient.mkₐ O J, surj := Ideal.Quotient.mkₐ_surjective O J
      homog := by rw [hkm]; exact hJh }
  choose N hN hN' using hn
  have hG : ∀ k : κ ⊕ κ', Sum.elim f N k ∈ wtPart O W.wt (Sum.elim wf wn k) := by
    rintro (k | k)
    · exact hf k
    · exact hN k
  have hG' : ∀ k : κ ⊕ κ', Ideal.Quotient.mk J (Sum.elim f N k) ∈ WA.part (Sum.elim wf wn k) :=
    fun k => ⟨_, hG k, rfl⟩
  refine ⟨_, inferInstance, inferInstance, inferInstance, WA, e, qh, fun k => ⟨_, WA.part_le_A (hG' k)⟩,
    fun _ => rfl, fun _ => rfl, hkm, ?_, hG', ?_, ?_⟩
  · intro y
    obtain ⟨y, rfl⟩ := hp y
    obtain ⟨F, rfl⟩ := W.surj y
    exact ⟨_, hqh F⟩
  · refine le_antisymm (fun y hy => ?_) (Ideal.span_le.2 ?_)
    · obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
      have h1 : W.π F ∈ (Ideal.span (Set.range N)).map W.π := by
        have h2 : W.π ∘ N = n := funext hN'
        rw [Ideal.map_span, ← Set.range_comp, h2, ← hk]
        exact hy
      obtain ⟨G, hG1, hG2⟩ := (Ideal.mem_map_iff_of_surjective _ W.surj).1 h1
      have h3 : F - G ∈ J ⊔ Ideal.span (Set.range f) := by
        rw [← hker, RingHom.mem_ker, map_sub, hG2, sub_self]
      have h4 : (J ⊔ Ideal.span (Set.range f)) ⊔ Ideal.span (Set.range N) ≤
          (Ideal.span (Set.range fun k => Ideal.Quotient.mk J (Sum.elim f N k))).comap (Ideal.Quotient.mk J) := by
        refine sup_le (sup_le (fun y hy => ?_) (Ideal.span_le.2 ?_)) (Ideal.span_le.2 ?_)
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
          exact zero_mem _
        · rintro _ ⟨k, rfl⟩
          exact Ideal.subset_span ⟨.inl k, rfl⟩
        · rintro _ ⟨k, rfl⟩
          exact Ideal.subset_span ⟨.inr k, rfl⟩
      have h5 := h4 (Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right hG1))
      rw [sub_add_cancel] at h5
      exact h5
    · rintro _ ⟨k | k, rfl⟩
      · have : W.π (f k) = 0 :=
          (hker ▸ Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩) : f k ∈ RingHom.ker W.π)
        show p (W.π (f k)) = 0
        rw [this, map_zero]
      · have : n k ∈ RingHom.ker p := hk ▸ Ideal.subset_span ⟨k, rfl⟩
        rw [← hN' k] at this
        exact this
  · rintro j _ ⟨F, hF, rfl⟩
    exact ⟨Ideal.Quotient.mk J F, ⟨F, hF, rfl⟩, rfl⟩

private theorem mop_card {α β : Type} [Finite α] [Finite β] (a : α → ℤ) (b : β → ℤ) (j : ℤ) :
    Nat.card {i // Sum.elim a b i = j} = Nat.card {i // a i = j} + Nat.card {i // b i = j} := by
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  rfl

private theorem mop_nWt : Nat.card {i // nWt i = -1} = 2 ∧ Nat.card {i // nWt i = -2} = 1 ∧
    Nat.card {i // nWt i = 1} = 2 ∧ Nat.card {i // nWt i = 2} = 1 ∧ Nat.card {i // nWt i = 0} = 2 := by
  simp only [Nat.card_eq_fintype_card]
  decide

private theorem mop_mat_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] {r : G →* GG 3 R}
    {W : WPres O ℤ R} (h : EntHomog r W) (g : G) (a b : Fin 3) : (r g).mat a b ∈ W.part (wt a b) := by
  rw [mat_eq_emb]
  exact add_mem (h g (.inl a) (.inl b)) (h g (.inl a) (.inr b))

private theorem mop_nEq_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] {r : G →* GG 3 R}
    {W : WPres O ℤ R} (h : EntHomog r W) (c g₁ : G) (k : Fin 8) : nEq c g₁ r k ∈ W.part (nWt k) := by
  have h1 : (1 : R) ∈ W.part 0 := SetLike.GradedOne.one_mem
  have hm := mop_mat_mem h
  fin_cases k
  · exact sub_mem (hm c 0 0) h1
  · exact sub_mem (hm c 1 1) h1
  · exact hm c 0 1
  · exact hm c 1 0
  · exact hm c 0 2
  · exact hm c 2 0
  · exact sub_mem (hm g₁ 0 1) (hm _ 0 1)
  · exact sub_mem (hm g₁ 1 0) (hm _ 1 0)

private theorem mop_der_coord {O : Type} [CommRing O] (s : ℤˣ) (t : Oˣ) (a b : Fin 3 ⊕ Fin 3) :
    ∃ (u : O) (a' b' : Fin 3), wt a' b' = wt6 a - wt6 b ∧
      ∀ {R Q : Type} [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q] (x : R →ₐ[O] O), ∀ D ∈ PtDer x Q,
        ∀ y : GG 3 R, GG.map (x : R →+* O) y = ⟨tor O t, s⟩ → ∀ c : O,
          D (emb y a b - algebraMap O R c) = u • D (y.mat a' b') := by
  obtain ⟨u, a', b', h1, h2⟩ := UpperTheory.exists_pointDerivation_emb_entry_eq_smul_mat_entry s t a b
  refine ⟨u, a', b', h1, fun x D hD y hy c => ?_⟩
  have h3 : D 1 = 0 := by simpa using hD 1 1
  rw [map_sub, h2 x D hD y hy, Algebra.algebraMap_eq_smul_one, map_smul, h3, smul_zero, sub_zero]

private theorem mop_main {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {K : Type} [NormedField K] [Algebra O K]
    (hpts : ∀ {R S : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
      (W : WPres O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
      RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
      ∀ ξ : W.A →ₐ[O] K, OnS (Ideal.span (Set.range g)) ξ →
        ∃ (t : Kˣ) (f : S →ₐ[O] K), IsLocPt f ∧ act W.gr (tz t) ξ = f.comp (qh.comp W.A.val))
    (hder : ∀ {R S : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing S] [Algebra O S] [IsCO O S]
      (W : WPres O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
      RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
      ∀ f : S →ₐ[O] K, IsLocPt f → ∀ D ∈ PtDer (f.comp (qh.comp W.A.val)) K, (∀ y ∈ Ideal.span (Set.range g), D y = 0) →
        ∃ F : S →ₐ[O] DualNumber K, dualFst F = f ∧ ∀ y : W.A, (F (qh y)).snd = D y)
    {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [Group H] [TopologicalSpace H]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
    {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁)
    (B : Univ (BoxCond N ι hι U I)) (WB : WPres O ℤ (U.R ⧸ I)) (hM : Marks η Ψ cc g₁) (hL : LocGood U I)
    (hΨ : CharCont Ψ) (hN : ∀ g ∈ N, r0 η Ψ g = 1) (hWB : IsLocPres U I WB) (hbox : BoxPres B WB) :
    Nonempty (Model S K) := by
  classical
  obtain ⟨W, i, τ, κ, _, _, e, f, wf, hrel, hi, hcoord, hent, hcount⟩ := hbox
  obtain ⟨x, τ₀, _, w, φ, hx, hφ, hdim⟩ := hL.chart
  obtain ⟨hB, hBx, φb, hφb⟩ := UpperTheory.exists_origin_and_chart_of_isLocPres U I x w φ WB hx hφ hWB
  obtain ⟨p, hp, hpr, hpk⟩ := UpperTheory.exists_surjection_univ_normCond_ker_span_nEq cc g₁ B S hM.csq hM.ηc
  have hIx : I ≤ RingHom.ker x := fun y hy => by
    rw [← hBx]
    show WB.origin hB (Ideal.Quotient.mk I y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]
  obtain ⟨x₀, hx₀, -⟩ := (S.rep O).2 (baseLift O η Ψ hΨ)
    ⟨baseRepGL3_normalised_of_psi_eq_one η Ψ g₁ hM.Ψc, hN, x, GLift.ext hx, hIx⟩
  have hbase : IsBase η Ψ S.r.hom x₀ := congrArg GLift.hom hx₀
  have hSr : S.r.hom = push p B.r.hom := (congrArg GLift.hom hpr).symm
  have hnorm : Normalised cc g₁ S.r.hom := ((S.rep S.R).1 (AlgHom.id _ _)).1
  obtain ⟨R, _, _, _, WA, ε, qh, g, hw, hz, hkA, hq, hg, hkq, hpart⟩ :=
    mop_cover WB i W e f wf hrel p hp (nEq cc g₁ B.r.hom) nWt (mop_nEq_mem hent cc g₁) hpk
  have hwl : ∀ s, WA.wt (ε (.inl s)) = WB.wt s := fun s => (hw _).trans (hrel.1 s)
  have hl : ∀ s, ∃ h a b, WB.wt s = wt6 a - wt6 b ∧
      WB.z s = Ideal.Quotient.mk I (emb (U.r.hom h) a b - algebraMap O U.R (emb (r0 η Ψ (ι h)) a b)) ∧
      qh (WA.z (ε (.inl s))) = emb (S.r.hom (ι h)) a b - algebraMap O S.R (emb (r0 η Ψ (ι h)) a b) := fun s => by
    obtain ⟨h, a, b, h1, h2⟩ := hWB.1 s
    have h3 : WB.z s = Ideal.Quotient.mkₐ O I
        (emb (U.r.hom h) a b - algebraMap O U.R (emb (r0 η Ψ (ι h)) a b)) := by
      rw [h2, map_sub, AlgHom.commutes, emb_push]
      rfl
    refine ⟨h, a, b, h1, h3, ?_⟩
    have h4 : W.z (e (.inl s)) = i (WB.z s) := by
      rw [WPres.z, WPres.z, ← hrel.2.1, MvPowerSeries.rename_X]
    rw [hz, h4, h3, ← AlgHom.comp_apply i, map_sub, AlgHom.commutes, ← emb_push, hi, map_sub, AlgHom.commutes,
      hSr, emb_push]
    rfl
  have hco : ∀ s, ∃ γ a b, WA.wt s = wt6 a - wt6 b ∧
      qh (WA.z s) = emb (S.r.hom γ) a b - algebraMap O S.R (emb (r0 η Ψ γ) a b) := fun s => by
    obtain ⟨s | t, rfl⟩ := ε.surjective s
    · obtain ⟨h, a, b, h1, -, h3⟩ := hl s
      exact ⟨ι h, a, b, (hwl s).trans h1, h3⟩
    · obtain ⟨γ, a, b, h1, h2⟩ := hcoord t
      refine ⟨γ, a, b, (hw _).trans h1, ?_⟩
      rw [hz, h2, map_sub, AlgHom.commutes, hSr, emb_push]
  have hz0 : ∀ s, x₀ (qh (WA.z s)) = 0 := fun s => by
    obtain ⟨γ, a, b, -, h2⟩ := hco s
    rw [h2]
    exact base_coord hbase γ a b
  obtain ⟨h, hor⟩ := origin_of WA (x₀.comp qh) hz0
  have hbd : ∀ s, -2 ≤ WA.wt s ∧ WA.wt s ≤ 2 := fun s => by
    obtain ⟨γ, a, b, h1, -⟩ := hco s
    rw [h1]
    exact blockWeight_sub_mem_Icc a b
  set a : ℤ → ℕ := fun j => Nat.card {t // W.wt (e (.inr t)) = j} with ha
  have ha0 : ∀ j, ¬ (-2 ≤ j ∧ j ≤ 2) → a j = 0 := fun j hj => by
    haveI : IsEmpty {t // W.wt (e (.inr t)) = j} := ⟨fun t => hj (by rw [← t.2, ← hw]; exact hbd _)⟩
    exact Nat.card_of_isEmpty
  have hcnt : ∀ j, Nat.card {u // wf u = j} = a j + boxDef j := hcount
  have hgb : ∀ k, -2 ≤ Sum.elim wf nWt k ∧ Sum.elim wf nWt k ≤ 2 := by
    rintro (k | k)
    · by_contra hj
      have h1 := hcnt (wf k)
      have h2 : boxDef (wf k) = 0 := if_neg fun h3 => hj (by
        have := abs_le.1 h3
        exact ⟨by show -2 ≤ wf k; omega, by show wf k ≤ 2; omega⟩)
      rw [ha0 (wf k) hj, h2] at h1
      haveI : Nonempty {u // wf u = wf k} := ⟨⟨k, rfl⟩⟩
      exact Nat.card_pos.ne' h1
    · revert k
      show ∀ k, -2 ≤ nWt k ∧ nWt k ≤ 2
      decide
  have hgq : ∀ k, qh (g k) = 0 := fun k =>
    (hkq ▸ Ideal.subset_span ⟨k, rfl⟩ : (g k : R) ∈ RingHom.ker qh)
  obtain ⟨n1, n2, n3, n4, n5⟩ := mop_nWt
  obtain ⟨Q, hQ⟩ := UpperTheory.exists_eqns_of_weighted_generators WA.gr (WA.originA h) (a (-1) + 2) (a (-2) + 1) (a 1 + 3) (a 2 + 1) (a 0 + 3) g
    (Sum.elim wf nWt) hg (fun k => by
      show WA.origin h (g k) = 0
      rw [hor, AlgHom.comp_apply, hgq, map_zero]) hgb
    (by rw [mop_card, hcnt, n1]; rfl) (by rw [mop_card, hcnt, n2]; rfl) (by rw [mop_card, hcnt, n3]; rfl)
    (by rw [mop_card, hcnt, n4]; rfl) (by rw [mop_card, hcnt, n5]; rfl)
  obtain ⟨h', ψ, hψ, -⟩ := chart_add O ℤ _ WB hB τ₀ w φb hφb R WA τ ε hwl hkA
  refine ⟨{
    A := WA.A
    𝒜 := WA.gr
    x := WA.originA h
    wring := isWRing O R WA h hbd
    r := a (-1) + 2
    s := a (-2) + 1
    r' := a 1 + 3
    s' := a 2 + 1
    m := a 0 + 3
    Q := Q
    one_le := by omega
    smooth := ⟨τ₀ ⊕ τ, inferInstance, _, _, chart_gr O ℤ R WA h _ _ ψ hψ, fun j => ?_⟩
    q := qh.comp WA.A.val
    ker_q := ?_
    x₀ := x₀
    base := hbase
    x₀_q := by rw [← AlgHom.comp_assoc, ← hor]; rfl
    ent := fun γ a b => ?_
    dense := fun j y hy n => ?_
    pts := ?_
    der := ?_
    lift := ?_ }⟩
  · simp only [hw]
    rw [mop_card, hdim]
    show locDims j + a j = _
    have := ha0 j
    unfold locDims mDims
    split_ifs <;> first | omega | (subst_vars; omega)
  · rw [hQ]
    ext y
    rw [← (homog_span O R ℤ WA _ g _ hg).2 y, ← hkq]
    rfl
  · obtain ⟨y, hy, hy'⟩ := hpart _ _ (mop_mat_mem hent γ a b)
    refine ⟨⟨y, WA.part_le_A hy⟩, hy, ?_⟩
    rw [hSr]
    exact hy'
  · obtain ⟨F, hF, hFy⟩ := hy
    have h1 : (qh.comp WA.A.val) y = (qh.comp WA.π) F := congrArg qh hFy.symm
    rw [h1]
    exact UpperTheory.exists_span_entMon_approx_of_mem_wtPart η Ψ S.r.hom cc ((S.r.hasMult cc).trans hM.ηc) hnorm.atc WA.wt (qh.comp WA.π) _
      (fun s => mem_max_of_zero x₀ (hz0 s)) hco j F hF n
  · rw [hQ]
    exact hpts WA h qh hq g _ hg hkq
  · rw [hQ]
    exact hder WA h qh hq g _ hg hkq
  · intro a₀ _ D hD hDw xl hxl D₁ hD₁ hD₁I hD₁w hcomp
    have hxx : xl = x := ((U.rep O).2 (U.r.map x) trivial).unique (GLift.ext (hxl.trans hx.symm)) rfl
    subst hxx
    let Db : (U.R ⧸ I) →ₗ[O] O := (Submodule.liftQ (I.restrictScalars O) D₁ hD₁I) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv O I).symm.toLinearMap
    have hDb : ∀ y, Db (Ideal.Quotient.mk I y) = D₁ y := fun _ => rfl
    have hxo : ∀ y, WB.origin hB (Ideal.Quotient.mk I y) = xl y := fun y => DFunLike.congr_fun hBx y
    refine UpperTheory.exists_base_pointDerivation_of_weight_homogeneous WB hB WA h ε hwl hkA qh x₀ hor.symm (Ideal.Quotient.mkₐ O _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective O _) (-1) D hD (fun s hs => ?_) Db (fun y y' => ?_) (fun s hs => ?_) fun s => ?_
    · obtain ⟨γ, a, b, h1, h2⟩ := hco s
      obtain ⟨u, a', b', h3, h4⟩ := mop_der_coord (η γ) (Ψ γ) a b
      rw [h2, h4 x₀ D hD _ (DFunLike.congr_fun hbase γ), hDw γ a' b' (by rwa [h3, ← h1]), smul_zero]
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y'
      rw [← map_mul, hDb, hDb, hDb, hxo, hxo]
      exact hD₁ y y'
    · obtain ⟨γ, a, b, h1, h2, -⟩ := hl s
      obtain ⟨u, a', b', h3, h4⟩ := mop_der_coord (η (ι γ)) (Ψ (ι γ)) a b
      rw [h2, hDb, h4 xl D₁ hD₁ _ (DFunLike.congr_fun hxl γ), hD₁w γ a' b' (by rwa [h3, ← h1]), smul_zero]
    · obtain ⟨γ, a, b, -, h2, h5⟩ := hl s
      obtain ⟨u, a', b', -, h4⟩ := mop_der_coord (η (ι γ)) (Ψ (ι γ)) a b
      rw [h2, h5, hDb, h4 xl D₁ hD₁ _ (DFunLike.congr_fun hxl γ), h4 x₀ D hD _ (DFunLike.congr_fun hbase (ι γ)),
        map_smul, ← hcomp]
      rfl

theorem UpperTheory.V.U3.model_of_pres :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (B : Univ (BoxCond N ι hι U I)) (WB : WPres c.O ℤ (U.R ⧸ I)),
      l ≠ 2 → Marks η Ψ cc g₁ → LocGood U I → CharCont Ψ → (∀ g ∈ N, r0 η Ψ g = 1) →
      IsLocPres U I WB → BoxPres B WB → Nonempty (Model S (PadicAlgCl l)) := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S B WB _ hM hL hΨ hN hWB hbox
  haveI := (UpperTheory.V.abelian₂.dvr_finite l c.O).1
  haveI : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  exact mop_main (@UpperTheory.exists_torus_twist_eq_localPoint_of_weightedPres l _ c) (@UpperTheory.exists_dualNumber_point_of_pointDerivation_vanishing l _ c) S B WB hM hL hΨ hN hWB hbox
