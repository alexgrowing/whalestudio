import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SysCover
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Loc_fin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.InLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.EltLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CloseMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CommLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimOut
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LimKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.selmer_cocycles_limit_and_descent_properties :
    S4 := by
  intro l _ L G0 T hT
  obtain ⟨Ph, i1, i2, i3, i4, i5, π, ct, hfg, hπ, hcomp⟩ := sys_cover l L G0 T hT
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Filter.hyperfilter_le_cofinite
  set K : Subgroup Ph := limKer (U : Filter ℕ) (fun N => (π N).ker) with hK
  have hKs := limKer_sup Ph ℕ U (fun N => (π N).ker)
  haveI : TotallyDisconnectedSpace (Ph ⧸ K) := (totallyDisconnected_quot Ph K hKs.1).1
  have sep : ∀ z : G0.Γ, (∀ W : OpenNormalSubgroup G0.Γ, z ∈ (W : Subgroup G0.Γ)) → z = 1 := by
    intro z hz
    have h1 := (totallyDisconnected_quot G0.Γ ⊥ (by simpa using isClosed_singleton)).2 z
      (fun O => by simpa using hz O)
    simpa using h1
  have swapW : ∀ (W : OpenNormalSubgroup G0.Γ) (a b : G0.Γ),
      b⁻¹ * a ∈ (W : Subgroup G0.Γ) → a * b⁻¹ ∈ (W : Subgroup G0.Γ) := by
    intro W a b h
    exact (Subgroup.Normal.mem_comm_iff inferInstance).1 h
  obtain ⟨F0, hF0c, hF0k, hF0u, hF0s⟩ := exists_lim_hom_out Ph G0.Γ ℕ hfg U (fun N => (π N).ker)
    (fun N => (T.h N).p.comp (π N)) (fun N => (T.h N).cont.comp (hπ N).1)
    (fun N x hx => by simp_all [MonoidHom.mem_ker])
  let hp : Ph ⧸ K →* G0.Γ := QuotientGroup.lift K F0 hF0k
  have hp_mk : ∀ g, hp (QuotientGroup.mk g) = F0 g := fun g => rfl
  have hp_cont : Continuous hp := by
    refine (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 ?_
    exact hF0c
  have hp_surj : Function.Surjective hp := by
    intro z
    obtain ⟨g, rfl⟩ := hF0s (fun N => ((T.h N).surj.comp (hπ N).2.1)) z
    exact ⟨_, hp_mk g⟩
  have unif : ∀ W : OpenNormalSubgroup G0.Γ, ∀ᶠ N in (U : Filter ℕ),
      ∀ g : Ph, (T.h N).p (π N g) * (hp (QuotientGroup.mk' K g))⁻¹ ∈ (W : Subgroup G0.Γ) := by
    intro W
    filter_upwards [hF0u W] with N hN g
    exact swapW W _ _ (hN g)
  have hct : hp (QuotientGroup.mk' K ct) = G0.c := by
    have h1 : ∀ W : OpenNormalSubgroup G0.Γ, (F0 ct)⁻¹ * G0.c ∈ (W : Subgroup G0.Γ) := by
      intro W
      obtain ⟨N, hN⟩ := (hF0u W).exists
      have h2 := hN ct
      simpa [(hπ N).2.2, (T.h N).c] using h2
    have h3 := sep _ h1
    exact (inv_mul_eq_one.1 h3)
  have modH : ∀ N (g : Ph), (T.h N).p (π N g) * (hp (QuotientGroup.mk' K g))⁻¹ ∈ (T.H : Subgroup G0.Γ) := by
    intro N g
    obtain ⟨M, hM⟩ := (unif T.H).exists
    have h1 := Subgroup.mul_mem _ (hcomp N M g) (hM g)
    simpa [mul_assoc] using h1
  have lift : ∀ (Y : Type) [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y]
      [TotallyDisconnectedSpace Y], PhiCond Y l → ∀ (f : ∀ N, Y →* (T.GN N).Γ) (f0 : Y →* G0.Γ),
      (∀ N, Continuous (f N)) → Continuous f0 → (∀ N y, (T.h N).p (f N y) = f0 y) →
      ∃ F : Y →* Ph ⧸ K, Continuous F ∧
        (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), ∀ y,
          Close (π N) (QuotientGroup.mk' K) (V : Subgroup Ph) (f N y) (F y)) ∧
        ∀ y, hp (F y) = f0 y := by
    intro Y _ _ _ _ _ hphi f f0 hfc hf0c hf
    obtain ⟨P, hPn, hPfg, hPker⟩ := loc_fin l Y (Subgroup.comap f0 (T.H : Subgroup G0.Γ))
      (T.H.toOpenSubgroup.isOpen.preimage hf0c) hphi
    obtain ⟨F, hFc, hFconv⟩ := in_lim Ph Y (fun N => (T.GN N).Γ) π U P f
      (fun N => ⟨(hπ N).1, (hπ N).2.1⟩) hPfg
      (fun N => ⟨hfc N, hPker _ (f N) (Subgroup.comap (T.h N).p (T.H : Subgroup G0.Γ)) (hfc N) (hT.2 N)
        (fun y hy => by simpa [Subgroup.mem_comap, hf] using hy)⟩)
    refine ⟨F, hFc, hFconv, fun y => ?_⟩
    refine close_map Ph (Ph ⧸ K) G0.Γ (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) (fun N => (T.h N).p) hp U
      (fun N => f N y) (F y) (f0 y) (hp_cont.comp continuous_quot_mk) unif
      (fun V => (hFconv V).mono fun N h => h y) (fun W => Filter.Eventually.of_forall fun N => ?_)
    simp [hf]
  have hv := fun v => lift (L.Gv v) (T.phiV v) (fun N => (T.GN N).η.ker.subtype.comp ((T.GN N).φ v))
    (G0.η.ker.subtype.comp (G0.φ v)) (fun N => continuous_subtype_val.comp ((T.GN N).φ_cont v))
    (continuous_subtype_val.comp (G0.φ_cont v)) (fun N y => (T.h N).φ v y)
  choose Fv hFvc hFvconv hFvp using hv
  have hu := fun u => lift (L.Gu u) (T.phiU u) (fun N => (T.GN N).η.ker.subtype.comp ((T.GN N).φu u))
    (G0.η.ker.subtype.comp (G0.φu u)) (fun N => continuous_subtype_val.comp ((T.GN N).φu_cont u))
    (continuous_subtype_val.comp (G0.φu_cont u)) (fun N y => (T.h N).φu u y)
  choose Fu hFuc hFuconv hFup using hu
  have memv : ∀ v y, Fv v y ∈ (G0.η.comp hp).ker := by
    intro v y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hFvp v y]
    exact (G0.φ v y).2
  have memu : ∀ u y, Fu u y ∈ (G0.η.comp hp).ker := by
    intro u y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hFup u y]
    exact (G0.φu u y).2
  let G : Glob l L :=
    { Γ := Ph ⧸ K
      η := G0.η.comp hp
      η_open := by
        rw [← MonoidHom.comap_ker]
        exact G0.η_open.preimage hp_cont
      c := QuotientGroup.mk' K ct
      c_sq := by
        rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        intro O
        refine Filter.Eventually.of_forall fun N => Subgroup.mem_sup_left ?_
        simp [MonoidHom.mem_ker, (hπ N).2.2, (T.GN N).c_sq]
      η_c := by
        rw [MonoidHom.comp_apply, hct, G0.η_c]
      ε := G0.ε.comp hp
      ε_cont := G0.ε_cont.comp hp_cont
      φ := fun v => (Fv v).codRestrict _ (memv v)
      φ_cont := fun v => (hFvc v).subtype_mk _
      φu := fun u => (Fu u).codRestrict _ (memu u)
      φu_cont := fun u => (hFuc u).subtype_mk _ }
  let h : G.Hom G0 :=
    { p := hp
      cont := hp_cont
      surj := hp_surj
      η := fun g => rfl
      c := hct
      ε := fun g => rfl
      φ := fun v g => hFvp v g
      φu := fun u g => hFup u g }
  have hPL : ∀ (W : OpenNormalSubgroup G0.Γ), PL l (T.H : Subgroup G0.Γ) ≤ (W : Subgroup G0.Γ) := by
    intro W
    rw [hT.1]
    exact bot_le
  have eph : ∀ j : Fin T.q, ∃ b : Ph ⧸ K, (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ),
      Close (π N) (QuotientGroup.mk' K) (V : Subgroup Ph) ((T.ph N j : (T.GN N).Γ)) b) ∧
      hp b = (T.sg j : G0.Γ) := by
    intro j
    obtain ⟨b, hb⟩ := elt_lim Ph (Ph ⧸ K) (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) U
      (fun N => (T.ph N j : (T.GN N).Γ)) (fun N => (hπ N).2.1)
    refine ⟨b, hb, ?_⟩
    exact close_map Ph (Ph ⧸ K) G0.Γ (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) (fun N => (T.h N).p) hp U
      (fun N => (T.ph N j : (T.GN N).Γ)) b _ (hp_cont.comp continuous_quot_mk) unif hb
      (fun W => hU (T.ph_lim W j (hPL W)))
  have eta : ∀ j : Fin T.q, ∃ b : Ph ⧸ K, (∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ),
      Close (π N) (QuotientGroup.mk' K) (V : Subgroup Ph) ((T.ta N j : (T.GN N).Γ)) b) ∧
      hp b = 1 := by
    intro j
    obtain ⟨b, hb⟩ := elt_lim Ph (Ph ⧸ K) (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) U
      (fun N => (T.ta N j : (T.GN N).Γ)) (fun N => (hπ N).2.1)
    refine ⟨b, hb, ?_⟩
    refine close_map Ph (Ph ⧸ K) G0.Γ (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) (fun N => (T.h N).p) hp U
      (fun N => (T.ta N j : (T.GN N).Γ)) b _ (hp_cont.comp continuous_quot_mk) unif hb
      (fun W => Filter.Eventually.of_forall fun N => ?_)
    simp [T.ta_ker N j]
  choose bph hbph hbphp using eph
  choose bta hbta hbtap using eta
  have memph : ∀ j, bph j ∈ G.η.ker := by
    intro j
    show G0.η (hp (bph j)) = 1
    rw [hbphp j]
    exact (T.sg j).2
  have memta : ∀ j, bta j ∈ G.η.ker := by
    intro j
    show G0.η (hp (bta j)) = 1
    rw [hbtap j, map_one]
  have hcomm : ∀ j, bph j * bta j = bta j * bph j := by
    intro j
    refine comm_lim l Ph (Ph ⧸ K) (fun N => (T.GN N).Γ) π (QuotientGroup.mk' K) U
      (fun N => (T.ph N j : (T.GN N).Γ)) (fun N => (T.ta N j : (T.GN N).Γ)) (fun N => T.Nq N j)
      (bph j) (bta j) hU (fun N => ⟨(hπ N).1, (hπ N).2.1⟩) continuous_quot_mk
      (fun V => by simpa [QuotientGroup.ker_mk'] using hKs.2.1 V) (hbph j) (hbta j)
      (fun N => T.Nq_mod N j) (fun N => ?_) (fun N W => ?_)
    · have e := T.tame N j
      rw [hT.2 N, Subgroup.mem_bot, OneMemClass.coe_eq_one, inv_mul_eq_one] at e
      have e2 := congrArg Subtype.val e
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at e2
      exact e2.symm
    · have hpl := (pl_props l (T.GN N).Γ (Subgroup.comap (T.h N).p (T.H : Subgroup G0.Γ))
        (T.H.toOpenSubgroup.isOpen.preimage (T.h N).cont)).2.2.2.1 W
      refine hpl.1 (by rw [hT.2 N]; exact bot_le) _ ?_
      simp [Subgroup.mem_comap, T.ta_ker N j]
  obtain ⟨s, hs, hsg⟩ := hfg
  exact ⟨
    { Ph := Ph
      fg := ⟨hs.toFinset, by simpa [topGen_iff] using hsg⟩
      U := U
      U_le := hU
      π := π
      π_cont := fun N => (hπ N).1
      π_surj := fun N => (hπ N).2.1
      G := G
      h := h
      πo := QuotientGroup.mk' K
      πo_cont := continuous_quot_mk
      πo_surj := QuotientGroup.mk'_surjective K
      modH := modH
      ct := ct
      ct_N := fun N => (hπ N).2.2
      ct_o := rfl
      ker_lim := fun V => by
        rw [QuotientGroup.ker_mk']
        exact hKs.2.1 V
      p_lim := unif
      φ_lim := fun V => Filter.eventually_all.2 fun v => hFvconv v V
      φu_lim := fun V => Filter.eventually_all.2 fun u => hFuconv u V
      ph := fun j => ⟨bph j, memph j⟩
      ta := fun j => ⟨bta j, memta j⟩
      ph_lim := fun V => Filter.eventually_all.2 fun j => hbph j V
      ta_lim := fun V => Filter.eventually_all.2 fun j => hbta j V
      comm := fun j => Subtype.ext (hcomm j)
      p_ph := fun j => Subtype.ext (hbphp j)
      p_ta := fun j => Subtype.ext (hbtap j) }⟩
