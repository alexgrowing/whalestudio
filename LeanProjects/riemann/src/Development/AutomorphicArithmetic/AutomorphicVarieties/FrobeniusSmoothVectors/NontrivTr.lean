import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrMap

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem rank_tr {k K G V : Type} [Field k] [Field K] (f : k →+* K) [Group G] [TopologicalSpace G]
    [CompactSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (χ : G →* kˣ)
    (χ' : G →* Kˣ) (h : ∀ g, χ' g = Units.map f.toMonoidHom (χ g)) :
    Module.rank K (H1C loc (chRep χ') fun _ => ⊥) = Module.rank k (H1C loc (chRep χ) fun _ => ⊥) ∧
    Module.rank K (H1C loc (chRep χ') fun _ => ⊤) = Module.rank k (H1C loc (chRep χ) fun _ => ⊤) := by
  have hχ : χ' = (Units.map (f : k →* K)).comp χ := MonoidHom.ext fun g => h g
  subst hχ
  exact ⟨(n4ch f loc χ (fun _ => ⊥) (fun _ => ⊥) (fun _ => Or.inl ⟨rfl, rfl⟩)).2,
    (n4ch f loc χ (fun _ => ⊤) (fun _ => ⊤) (fun _ => Or.inr ⟨rfl, rfl⟩)).2⟩

private theorem nontriv_tr {k K M N : Type} [Field k] [Field K] [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module K N] (e : Module.rank K N = Module.rank k M) (h : Nontrivial M) : Nontrivial N := by
  rw [← rank_pos_iff_nontrivial (R := K), e]
  exact rank_pos_iff_nontrivial.2 h

theorem UpperTheory.V.Fr.ok_ext :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {k' : Type} [Field k'] [Finite k'] [CharP k' l] (f : k →+* k'), F.Ok C₀ → (F.ext f).Ok C₀ := by
  intro l _ k _ _ F C₀ k' _ _ _ f h
  have hinj : Function.Injective f := f.injective
  have hU : ∀ u v : kˣ, Units.map (f : k →* k') u = Units.map (f : k →* k') v → u = v := by
    intro u v huv
    ext
    apply hinj
    simpa using congrArg Units.val huv
  have hU1 : ∀ u : kˣ, Units.map (f : k →* k') u = 1 → u = 1 := by
    intro u hu
    apply hU
    rw [hu, map_one]
  have hΨ : ∀ g, (F.ext f).Ψ g = Units.map (f : k →* k') (F.Ψ g) := fun g => rfl
  have hz : ∀ x : ZMod l, f (ZMod.castHom (dvd_refl l) k x) = ZMod.castHom (dvd_refl l) k' x :=
    fun x => RingHom.congr_fun
      (Subsingleton.elim (f.comp (ZMod.castHom (dvd_refl l) k)) (ZMod.castHom (dvd_refl l) k')) x
  have hom : ∀ g, (F.ext f).om k' g = Units.map (f : k →* k') (F.om k g) := by
    intro g
    ext
    change ((ZMod.castHom (dvd_refl l) k').comp PadicInt.toZMod) ((F.eps g : ℤ_[l])) =
      f (((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) ((F.eps g : ℤ_[l])))
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact (hz _).symm
  have hdel : ∀ g, (F.ext f).delK k' g = Units.map (f : k →* k') (F.delK k g) := by
    intro g
    ext
    change (Int.castRingHom k') (F.del g : ℤ) = f ((Int.castRingHom k) (F.del g : ℤ))
    simp
  have hker : (F.ext f).Ψ.ker = F.Ψ.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    exact ⟨hU1 _, fun h1 => by rw [hΨ, h1, map_one]⟩
  haveI : CompactSpace F.G0 :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ h.del_open).isCompact
  have hχ1 : ∀ g : F.Γ, ((F.ext f).Ψ⁻¹ * (F.ext f).delK k') g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹ * F.delK k) g) := by
    intro g
    change ((F.ext f).Ψ g)⁻¹ * (F.ext f).delK k' g = Units.map f.toMonoidHom ((F.Ψ g)⁻¹ * F.delK k g)
    erw [hdel, hΨ, map_mul, map_inv]
    rfl
  have hχ2 : ∀ g : F.Γ, ((F.ext f).Ψ⁻¹ ^ 2 * (F.ext f).delK k') g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹ ^ 2 * F.delK k) g) := by
    intro g
    rw [pow_two, pow_two]
    change ((F.ext f).Ψ g)⁻¹ * ((F.ext f).Ψ g)⁻¹ * (F.ext f).delK k' g =
      Units.map f.toMonoidHom ((F.Ψ g)⁻¹ * (F.Ψ g)⁻¹ * F.delK k g)
    erw [hdel, hΨ, map_mul, map_mul, map_inv]
    rfl
  have hχ3 : ∀ g : F.G0, ((F.ext f).Ψ⁻¹.comp (F.ext f).del.ker.subtype) g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹.comp F.del.ker.subtype) g) := by
    intro g
    change (Units.map (f : k →* k') (F.Ψ (g : F.Γ)))⁻¹ = Units.map f.toMonoidHom ((F.Ψ (g : F.Γ))⁻¹)
    rw [map_inv]
    rfl
  have hχ4 : ∀ g : F.Γ, (1 : F.Γ →* k'ˣ) g = Units.map f.toMonoidHom ((1 : F.Γ →* kˣ) g) := by
    intro g
    rw [MonoidHom.one_apply, MonoidHom.one_apply, map_one]
  exact
    { l_odd := h.l_odd
      fin := inferInstance
      del_open := h.del_open
      c_sq := h.c_sq
      del_c := h.del_c
      loc_cont := h.loc_cont
      eps_cont := h.eps_cont
      Ψ_open := by rw [hker]; exact h.Ψ_open
      Ψ_c := by
        show Units.map (f : k →* k') (F.Ψ F.c) = 1
        rw [h.Ψ_c, map_one]
      baseSubgroup_spec := fun he => h.baseSubgroup_spec (hU1 _ (by rw [map_pow]; exact he))
      phi := h.phi
      card_inf := h.card_inf
      cw_sq := h.cw_sq
      del_cw := h.del_cw
      f2a := by
        obtain ⟨g, hg⟩ := h.f2a
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        rw [hom] at he
        exact he
      f2b := by
        intro j hj
        obtain ⟨g, hg⟩ := h.f2b j hj
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        rw [hom, hΨ] at he
        rw [map_mul, map_zpow]
        exact he
      f2c := by
        intro j hj
        obtain ⟨g, hg⟩ := h.f2c j hj
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        erw [hom, hdel] at he
        rw [map_mul, map_mul, map_zpow]
        exact he
      f3 := by
        intro v
        obtain ⟨g, hg⟩ := h.f3 v
        exact ⟨g, fun he => hg (hU1 _ (by rw [map_pow]; exact he))⟩
      f4 := nontriv_tr (rank_tr f F.loc _ _ hχ1).1 h.f4
      f4' := nontriv_tr (rank_tr f F.loc _ _ hχ2).1 h.f4'
      f5 := by
        rintro ⟨j, hj⟩
        refine h.f5 ⟨j, fun g => hU _ _ ?_⟩
        have hg := hj g
        rw [hom, hΨ] at hg
        rw [map_zpow]
        exact hg
      Ψ_N := fun v g hg => by
        show Units.map (f : k →* k') (F.Ψ (F.loc v g)) = 1
        rw [h.Ψ_N v g hg, map_one]
      gen := by
        intro v
        obtain ⟨u, a₀, h1, h2, h3⟩ := h.gen v
        refine ⟨u, a₀, fun a => ⟨(h1 a).1, ?_⟩, h2, h3⟩
        show Units.map (f : k →* k') (F.Ψ (F.loc v (u a))) = 1
        rw [(h1 a).2, map_one]
      cl := h.cl
      ec := h.ec
      b1p := (rank_tr f F.loc _ _ hχ2).1.trans_le h.b1p
      b1 := (rank_tr f F.loc2 _ _ hχ3).1.trans_le h.b1
      h1 := (rank_tr f F.loc _ _ hχ4).2.trans_le h.h1 }
