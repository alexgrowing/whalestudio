import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem card_ker_range {A V W : Type} [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (f : V →ₗ[A] W) : Nat.card V = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]

private def Zu {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (M : FRep A G) (J : Subgroup G) :
    Submodule A (G → M.X) where
  carrier := {z | z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0}
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨add_mem a1 b1, fun g hg => by rw [Pi.add_apply, a2 g hg, b2 g hg, add_zero]⟩
  smul_mem' := by
    rintro c a ⟨a1, a2⟩
    exact ⟨Submodule.smul_mem _ c a1, fun g hg => by rw [Pi.smul_apply, a2 g hg, smul_zero]⟩

private theorem card_Zu {l : ℕ} [Fact l.Prime] {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (h : UnrCount l G J) (M : FRep A G) (hl : ∀ m : M.X, l • m = 0) (hJ : ∀ g ∈ J, ∀ m, M.ρ g m = m) :
    Finite (Zu M J) ∧ Nat.card (Zu M J) = Nat.card M.X := by
  have hLC : LC M.ρ := by
    intro m
    rw [IsLocallyConstant.iff_continuous]
    exact M.cont.comp (continuous_id.prodMk continuous_const)
  have hJ' : ∀ g ∈ J, M.ρ g = 1 := fun g hg => LinearMap.ext (hJ g hg)
  obtain ⟨hfin, hcard⟩ := h A M.X M.ρ hLC hl hJ'
  have hset : ((Zu M J : Submodule A (G → M.X)) : Set (G → M.X)) =
      {z | z ∈ Zl M.ρ ∧ ∀ g ∈ J, z g = 0} := by
    ext z
    show (z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0) ↔ _
    rw [mem_Z1_iff_cocycle, Set.mem_setOf_eq, mem_Zl, IsLocallyConstant.iff_continuous]
  have e : (Zu M J) ≃ {z | z ∈ Zl M.ρ ∧ ∀ g ∈ J, z g = 0} := Equiv.setCongr hset
  refine ⟨?_, ?_⟩
  · haveI := hfin.to_subtype
    exact Finite.of_equiv _ e.symm
  · rw [Nat.card_congr e, Nat.card_coe_set_eq, hcard]

private def kerRep {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (M M' : FRep A G) (u : M.X →ₗ[A] M'.X)
    (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m)) : FRep A G where
  X := LinearMap.ker u
  ρ := Representation.subrepresentation M.ρ (LinearMap.ker u) (fun g m hm => by
    show u (M.ρ g m) = 0
    rw [hu, LinearMap.mem_ker.1 hm, map_zero])
  cont := Continuous.subtype_mk (M.cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _

private theorem comp_mem_Zu_of_equivariant {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M M' : FRep A G) (u : M.X →ₗ[A] M'.X) (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m))
    (z : G → M.X) (hz : z ∈ Zu M J) : (fun g => u (z g)) ∈ Zu M' J := by
  have hz' : z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0 := hz
  have hzc := (mem_Z1_iff_cocycle _ _).1 hz'.1
  show (fun g => u (z g)) ∈ Z1 M'.ρ ∧ ∀ g ∈ J, (fun g => u (z g)) g = 0
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · exact (continuous_of_discreteTopology (f := u)).comp hzc.1
  · intro g h
    simp only [hzc.2 g h, map_add, hu]
  · intro g hg
    simp only [hz'.2 g hg, map_zero]

private theorem d0_mem_Zu_of_trivial_on {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M : FRep A G) (hJ : ∀ g ∈ J, ∀ m, M.ρ g m = m) (m : M.X) : d0 M.ρ m ∈ Zu M J := by
  have hd : ∀ g, d0 M.ρ m g = M.ρ g m - m := fun g => rfl
  show d0 M.ρ m ∈ Z1 M.ρ ∧ ∀ g ∈ J, d0 M.ρ m g = 0
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · have hc : Continuous fun g => M.ρ g m := M.cont.comp (continuous_id.prodMk continuous_const)
    exact (hc.sub continuous_const).congr (fun g => (hd g).symm)
  · intro g h
    rw [hd, hd, hd, map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro g hg
    rw [hd, hJ g hg, sub_self]

private theorem ker_restrict_mem_Zu_of_comp_zero {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M M' : FRep A G) (u : M.X →ₗ[A] M'.X) (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m))
    (z : G → M.X) (hz : z ∈ Zu M J) (hk : ∀ g, u (z g) = 0) :
    (fun g => (⟨z g, LinearMap.mem_ker.2 (hk g)⟩ : LinearMap.ker u)) ∈ Zu (kerRep M M' u hu) J := by
  have hz' : z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0 := hz
  have hzc := (mem_Z1_iff_cocycle _ _).1 hz'.1
  show _ ∈ Z1 (kerRep M M' u hu).ρ ∧ _
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · exact hzc.1.subtype_mk _
  · intro g h
    exact Subtype.ext (hzc.2 g h)
  · intro g hg
    exact Subtype.ext (hz'.2 g hg)

theorem UpperTheory.V.Pa.B2.urOf :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), UnrCount l G J → UrAx l J := by
  intro l _ G _ _ _ J h
  unfold UrAx
  intro A _ M hl hJ
  have memZu : ∀ {N : FRep A G} {z : G → N.X}, z ∈ Zu N J ↔ z ∈ Z1 N.ρ ∧ ∀ g ∈ J, z g = 0 :=
    Iff.rfl
  obtain ⟨hfin, hcZ⟩ := card_Zu h M hl hJ
  refine ⟨?_, ?_⟩
  · have hZ : Zu M J ≤ Z1 M.ρ := fun z hz => (memZu.1 hz).1
    have hres : ∀ w : Z1 M.ρ, resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk (restrictCocycles1 M.ρ J.subtype continuous_subtype_val w) := fun w => rfl
    let φ0 : Zu M J →ₗ[A] H1 M.ρ := (Submodule.mkQ _) ∘ₗ Submodule.inclusion hZ
    have hφ0 : ∀ z, φ0 z ∈ H1ur M.ρ J := by
      intro z
      rw [H1ur, LinearMap.mem_ker]
      show resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk (Submodule.inclusion hZ z)) = 0
      rw [hres]
      have hz0 : restrictCocycles1 M.ρ J.subtype continuous_subtype_val (Submodule.inclusion hZ z) = 0 :=
        Subtype.ext (funext fun x => (memZu.1 z.2).2 x x.2)
      rw [hz0, Submodule.Quotient.mk_zero]
    let φ : Zu M J →ₗ[A] H1ur M.ρ J := φ0.codRestrict _ hφ0
    let d : M.X →ₗ[A] Zu M J := (d0 M.ρ).codRestrict _ (d0_mem_Zu_of_trivial_on M hJ)
    have hsurj : Function.Surjective φ := by
      rintro ⟨c, hc⟩
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      rw [H1ur, LinearMap.mem_ker] at hc
      change resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk w) = 0 at hc
      rw [hres, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hc
      obtain ⟨m, hm⟩ := hc
      have hwJ : ∀ g ∈ J, w.1 g = 0 := by
        intro g hg
        have hh := hm ⟨g, hg⟩
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hJ g hg, sub_self] at hh
        exact hh
      refine ⟨⟨w.1, memZu.2 ⟨w.2, hwJ⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
    have hker : LinearMap.ker d = H0 M.ρ := by
      ext m
      rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
      constructor
      · intro hm g
        have hh : M.ρ g m - m = 0 := congrArg (fun z : Zu M J => z.1 g) hm
        exact sub_eq_zero.1 hh
      · intro hm
        apply Subtype.ext
        funext g
        exact (sub_eq_zero.2 (hm g) : M.ρ g m - m = 0)
    have hrange : LinearMap.range d = LinearMap.ker φ := by
      ext z
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨m, rfl⟩
        apply Subtype.ext
        show (Submodule.Quotient.mk (Submodule.inclusion hZ (d m)) : H1 M.ρ) = 0
        apply (Submodule.Quotient.mk_eq_zero (Submodule.comap (Z1 M.ρ).subtype (B1 M.ρ))).2
        show d0 M.ρ m ∈ B1 M.ρ
        exact (mem_coboundaries1 _ _).2 ⟨m, fun g => rfl⟩
      · intro hz
        have hz2 : (Submodule.Quotient.mk (Submodule.inclusion hZ z) : H1 M.ρ) = 0 :=
          congrArg Subtype.val hz
        have hB : z.1 ∈ B1 M.ρ :=
          (Submodule.Quotient.mk_eq_zero (Submodule.comap (Z1 M.ρ).subtype (B1 M.ρ))).1 hz2
        obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hB
        exact ⟨m, Subtype.ext (funext fun g => (hm g).symm)⟩
    have hrφ : Nat.card (LinearMap.range φ) = Nat.card (H1ur M.ρ J) := by
      rw [LinearMap.range_eq_top.2 hsurj]
      exact Nat.card_congr Submodule.topEquiv.toEquiv
    haveI := hfin
    have e1 := card_ker_range d
    have e2 := card_ker_range φ
    rw [hker, hrange] at e1
    rw [hrφ, hcZ, e1] at e2
    have hpos : 0 < Nat.card (LinearMap.ker φ) := Nat.card_pos
    rw [mul_comm] at e2
    exact (Nat.eq_of_mul_eq_mul_left hpos e2).le
  · intro M' u hu hsu y' hy' hy'J
    have hl' : ∀ m : M'.X, l • m = 0 := by
      intro m
      obtain ⟨x, rfl⟩ := hsu m
      rw [← map_nsmul, hl, map_zero]
    have hJ' : ∀ g ∈ J, ∀ m : M'.X, M'.ρ g m = m := by
      intro g hg m
      obtain ⟨x, rfl⟩ := hsu m
      rw [← hu, hJ g hg]
    obtain ⟨hfin', hcZ'⟩ := card_Zu h M' hl' hJ'
    let K := kerRep M M' u hu
    have hlK : ∀ m : K.X, l • m = 0 := fun m => Subtype.ext (hl m.1)
    have hJK : ∀ g ∈ J, ∀ m : K.X, K.ρ g m = m := fun g hg m => Subtype.ext (hJ g hg m.1)
    obtain ⟨-, hcZK⟩ := card_Zu h K hlK hJK
    let ψ : Zu M J →ₗ[A] Zu M' J := ((u.compLeft G) ∘ₗ (Zu M J).subtype).codRestrict _
      (fun z => comp_mem_Zu_of_equivariant M M' u hu z.1 z.2)
    let ι : Zu K J →ₗ[A] Zu M J := (((LinearMap.ker u).subtype.compLeft G) ∘ₗ (Zu K J).subtype).codRestrict _
      (fun w => comp_mem_Zu_of_equivariant K M (LinearMap.ker u).subtype (fun g m => rfl) w.1 w.2)
    have hιinj : Function.Injective ι := by
      intro a b hab
      apply Subtype.ext
      funext g
      exact Subtype.ext (congrArg (fun z : Zu M J => z.1 g) hab)
    have hιr : LinearMap.range ι = LinearMap.ker ψ := by
      ext z
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨w, rfl⟩
        apply Subtype.ext
        funext g
        exact LinearMap.mem_ker.1 (w.1 g).2
      · intro hz
        have hk : ∀ g, u (z.1 g) = 0 := fun g => congrArg (fun y : Zu M' J => y.1 g) hz
        exact ⟨⟨_, ker_restrict_mem_Zu_of_comp_zero M M' u hu z.1 z.2 hk⟩, Subtype.ext rfl⟩
    have hcM : Nat.card M.X = Nat.card K.X * Nat.card M'.X := by
      have e := card_ker_range u
      rw [LinearMap.range_eq_top.2 hsu, Nat.card_congr Submodule.topEquiv.toEquiv] at e
      exact e
    have e2 := card_ker_range ψ
    rw [← hιr, Nat.card_congr (LinearEquiv.ofInjective ι hιinj).symm.toEquiv, hcZ, hcZK, hcM] at e2
    have hposK : 0 < Nat.card K.X := Nat.card_pos
    have hrψ : Nat.card (LinearMap.range ψ) = Nat.card (Zu M' J) := by
      rw [hcZ']
      exact (Nat.eq_of_mul_eq_mul_left hposK e2).symm
    haveI := hfin'
    have htop : (LinearMap.range ψ).toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq _ hrψ
    have hmem : (⟨y', memZu.2 ⟨hy', hy'J⟩⟩ : Zu M' J) ∈ LinearMap.range ψ := by
      have hh : (⟨y', memZu.2 ⟨hy', hy'J⟩⟩ : Zu M' J) ∈ (LinearMap.range ψ).toAddSubgroup := by
        rw [htop]
        exact AddSubgroup.mem_top _
      exact hh
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hmem
    exact ⟨z.1, (memZu.1 z.2).1, (memZu.1 z.2).2, fun g => congrArg (fun y : Zu M' J => y.1 g) hz⟩
