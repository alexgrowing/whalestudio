import Development.EtaleCohomology.EtaleSheaves.AugBij

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.AugBijPf

def Sep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (T : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T),
  (∀ i, Etale (g i)) → (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) →
  ∀ x y : Sec F T, (∀ i, Sec.res (g i) x = Sec.res (g i) y) → x = y

def Glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (T : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T),
  (∀ i, Etale (g i)) → (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) →
  ∀ x : ∀ i, Sec F (V i), (∀ i j, Sec.res (pullback.fst (g i) (g j)) (x i) = Sec.res (pullback.snd (g i) (g j)) (x j)) →
  ∃ y : Sec F T, ∀ i, Sec.res (g i) y = x i

def LocSurj : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → ∀ f : LocallyConstant T (ZMod q),
  ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧ (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧
    ∀ i, ∃ y : Sec (tw q 0) (V i), φ (V i) y = f.comap (g i).base.hom

def LocInj : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → ∀ x : Sec (tw q 0) T, φ T x = 0 →
  ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧ (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧
    ∀ i, Sec.res (g i) x = 0

theorem unit_res {q : ℕ} {V T : Scheme.{0}} (g : V ⟶ T) (h : IsUnit (q : Γ(T, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res f (Sec.res g x) = Sec.res (f ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sheafFor {R : Type} [CommRing R] (F : Shv R) {T : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (g : ∀ i, V i ⟶ T)
    (he : ∀ i, Etale (g i)) (hs : ∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) :
    (Presieve.ofArrows V g).IsSheafFor (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
  have h1 : Presheaf.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property
  have h2 := (isSheaf_iff_isSheaf_of_type _ _).1 h1
  refine Presieve.IsSheaf.isSheafFor_of_mem_precoverage (J := Scheme.precoverage @Etale) h2 ?_
  exact (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => by obtain ⟨i, v, hv⟩ := hs x; exact ⟨i, v, hv⟩, he⟩

theorem Sep_holds : Sep := by
  intro R _ F T ι V g he hs x y hxy
  have h := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).1 (sheafFor F g he hs) (fun i => Sec.res (g i) y) (by
    intro i j
    change Sec.res _ (Sec.res _ y) = Sec.res _ (Sec.res _ y)
    rw [res_comp, res_comp, pullback.condition])
  exact h.unique (fun i => hxy i) (fun i => rfl)

theorem Glue_holds : Glue := by
  intro R _ F T ι V g he hs x hx
  obtain ⟨y, hy, -⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks _ _).1 (sheafFor F g he hs) x hx
  exact ⟨y, hy⟩

def Root : Prop := ∀ (q : ℕ) (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  ∃ (W : Scheme.{0}) (h : W ⟶ U), Etale h ∧ (∀ u : U, ∃ w : W, h.base w = u) ∧ Nonempty (Prim q Γ(W, ⊤))

theorem LocSurj_of (hR : Root) : LocSurj := by
  intro q φ hnat hgen T hT f
  let O : ZMod q → T.Opens := fun c => ⟨{t | f t = c}, f.isLocallyConstant.isOpen_fiber c⟩
  choose W h he hs hζ using fun c => hR q (O c) (unit_res (O c).ι hT)
  refine ⟨ZMod q, W, fun c => h c ≫ (O c).ι, fun c => by haveI := he c; infer_instance, ?_, ?_⟩
  · intro t
    have ht : t ∈ Set.range (O (f t)).ι.base := by rw [Scheme.Opens.range_ι]; exact (rfl : f t = f t)
    obtain ⟨u, hu⟩ := ht
    obtain ⟨w, hw⟩ := hs (f t) u
    exact ⟨f t, w, by rw [Scheme.Hom.comp_apply, hw, hu]⟩
  · intro c
    refine ⟨((c.cast : ℤ)) • twGen 0 (hζ c).some, ?_⟩
    rw [map_zsmul, hgen]
    ext w
    have hm : ((O c).ι.base (h c w)) ∈ O c := by
      have hr : ((O c).ι.base (h c w)) ∈ Set.range (O c).ι.base := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at hr; exact hr
    have hm' : f ((O c).ι.base (h c w)) = c := hm
    have e1 : ((c.cast : ℤ) • (1 : LocallyConstant (W c) (ZMod q))) w = c := by
      change (c.cast : ℤ) • (1 : ZMod q) = c
      rw [zsmul_eq_mul, mul_one, ZMod.intCast_cast, ZMod.cast_id', id_eq]
    rw [e1, LocallyConstant.coe_comap, Function.comp_apply]
    erw [Scheme.Hom.comp_apply]
    exact hm'.symm

theorem AugBij_of_loc (hS : Sep) (hG : Glue) (hSu : LocSurj) (hI : LocInj) : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij := by
  intro q φ hnat hgen
  have inj : ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → Function.Injective (φ T) := by
    intro T hT
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨ι, V, g, he, hs, h0⟩ := hI q φ hnat hgen T hT x hx
    exact hS _ _ T ι V g he hs x 0 (fun i => by rw [h0 i]; exact (map_zero ((tw q 0).obj.map (g i).op).hom).symm)
  intro T hT
  refine ⟨inj T hT, fun f => ?_⟩
  obtain ⟨ι, V, g, he, hs, hy⟩ := hSu q φ hnat hgen T hT f
  choose y hy using hy
  obtain ⟨z, hz⟩ := hG _ _ T ι V g he hs y (fun i j => by
    apply inj _ (unit_res (pullback.fst (g i) (g j) ≫ g i) hT)
    rw [hnat, hnat, hy i, hy j]
    ext t
    simp only [LocallyConstant.coe_comap, Function.comp_apply]
    erw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rfl)
  refine ⟨z, ?_⟩
  ext t
  obtain ⟨i, v, rfl⟩ := hs t
  have := congrArg (fun k : LocallyConstant (V i) (ZMod q) => k v) ((hnat (g i) z).symm.trans ((congrArg (φ (V i)) (hz i)).trans (hy i)))
  simpa using this

def SecLoc : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (T : Scheme.{0})
  (x : Sec (ofRings R M) T), ∃ (ι : Type) (V : ι → Scheme.{0}) (g : ∀ i, V i ⟶ T), (∀ i, Etale (g i)) ∧
    (∀ t : T, ∃ i, ∃ v : V i, (g i).base v = t) ∧ ∀ i, ∃ a : M.obj Γ(V i, ⊤), Sec.res (g i) x = ofRings.sec M (V i) a

def GenEq : Prop := ∀ (q : ℕ) (U : Scheme.{0}) (ξ ζ : Prim q Γ(U, ⊤)), twGen 0 ξ = twGen 0 ζ

theorem secEq (hE : GenEq) {q : ℕ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (a : (twF q 0).obj Γ(U, ⊤)) :
    ∃ m : ℤ, ofRings.sec (twF q 0) U a = m • twGen 0 ζ := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
  induction a using Finsupp.induction_linear with
  | zero => exact ⟨0, by rw [zero_smul]; exact map_zero ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom⟩
  | add a b ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    rw [add_smul, ← hm, ← hn, Submodule.Quotient.mk_add]
    exact map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom _ _
  | single ξ c =>
    refine ⟨(c.down.cast : ℤ), ?_⟩
    have h1 : Finsupp.single ξ c = c • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, Submodule.Quotient.mk_smul]
    have h2 : ofRings.sec (twF q 0) U (c • Submodule.Quotient.mk (Finsupp.single ξ 1)) =
        c • twGen 0 ξ := map_smul ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app _).hom _ _
    refine h2.trans ?_
    rw [hE q U ξ ζ, ← Int.cast_smul_eq_zsmul (ULift.{1} (ZMod q))]
    congr 1
    apply ULift.ext
    rw [ULift.down_intCast, ZMod.intCast_cast, ZMod.cast_id', id_eq]

theorem LocInj_of (hR : Root) (hL : SecLoc) (hE : GenEq) : LocInj := by
  intro q φ hnat hgen T hT x hx
  obtain ⟨W, h, he, hs, ⟨ζ⟩⟩ := hR q T hT
  obtain ⟨ι, V, g, hge, hgs, ha⟩ := hL (ZMod q) (twF q 0) W (Sec.res h x)
  choose a ha using ha
  refine ⟨{i // Nonempty (V i)}, fun i => V i.1, fun i => g i.1 ≫ h, fun i => by haveI := hge i.1; haveI := he; infer_instance,
    ?_, ?_⟩
  · intro t
    obtain ⟨w, rfl⟩ := hs t
    obtain ⟨i, v, rfl⟩ := hgs w
    exact ⟨⟨i, ⟨v⟩⟩, v, by rw [Scheme.Hom.comp_apply]⟩
  · rintro ⟨i, ⟨v⟩⟩
    obtain ⟨m, hm⟩ := secEq hE (ζ.map (g i).appTop.hom) (a i)
    have hx' : Sec.res (g i ≫ h) x = m • twGen 0 (ζ.map (g i).appTop.hom) :=
      (res_comp (g i) h x).symm.trans ((ha i).trans hm)
    have h0 : φ (V i) (Sec.res (g i ≫ h) x) = 0 := by rw [hnat, hx]; rfl
    rw [hx', map_zsmul, hgen] at h0
    have h3 : (m : ZMod q) = 0 := by
      have := congrArg (fun k : LocallyConstant (V i) (ZMod q) => k v) h0
      change m • (1 : ZMod q) = 0 at this
      rwa [zsmul_eq_mul, mul_one] at this
    show Sec.res (g i ≫ h) x = 0
    rw [hx', ← Int.cast_smul_eq_zsmul (ULift.{1} (ZMod q))]
    have h4 : ((m : ULift.{1} (ZMod q))) = 0 := by apply ULift.ext; simpa using h3
    rw [h4, zero_smul]

theorem secLoc' : SecLoc := by
  intro R _ M T x
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ M)) (U := Opposite.op T) x
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hmem
  have hc := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).1 𝒰.mem₀
  refine ⟨𝒰.I₀, 𝒰.X, 𝒰.f, hc.2, fun t => ?_, fun i => ?_⟩
  · obtain ⟨i, v, hv⟩ := hc.1 t; exact ⟨i, v, hv⟩
  · obtain ⟨a, ha⟩ := @h𝒰 _ (𝒰.f i) (by exact Presieve.ofArrows.mk i)
    exact ⟨a, ha.symm⟩

theorem twGen_res {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen 0 ζ) = twGen 0 (ζ.map g.appTop.hom) := by
  have h := congrArg (fun k => (ModuleCat.Hom.hom k) (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))))
    ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)).naturality g.op)
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)).app (Opposite.op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem twGen_eq_of_pow {q : ℕ} {U : Scheme.{0}} (ξ ζ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  apply (Submodule.Quotient.eq _).2
  apply Submodule.subset_span
  refine ⟨ζ, ξ, a, h, ?_⟩
  simp
  rfl

def ZarPow : Prop := ∀ (q : ℕ) (U : Scheme.{0}) (ξ ζ : Prim q Γ(U, ⊤)) (u : U),
  ∃ (O : U.Opens) (a : (ZMod q)ˣ), u ∈ O ∧ (ξ.map O.ι.appTop.hom).1 = (ζ.map O.ι.appTop.hom).1 ^ (a : ZMod q).val

theorem GenEq_of (hZ : ZarPow) : GenEq := by
  intro q U ξ ζ
  choose O a hu ha using hZ q U ξ ζ
  refine Sep_holds (ZMod q) (tw q 0) U U (fun u => (O u : Scheme.{0})) (fun u => (O u).ι) (fun u => inferInstance) ?_ _ _ ?_
  · intro t
    have ht : t ∈ Set.range (O t).ι.base := by rw [Scheme.Opens.range_ι]; exact hu t
    obtain ⟨v, hv⟩ := ht
    exact ⟨t, v, hv⟩
  · intro u
    rw [twGen_res, twGen_res]
    exact twGen_eq_of_pow _ _ (a u) (ha u)

def LocPow : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (ξ ζ : Prim q A),
  ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val

theorem ZarPow_of (hL : LocPow) : ZarPow := by
  intro q U ξ ζ u
  obtain ⟨a, ha⟩ := hL q (U.presheaf.stalk u) (ξ.map (U.presheaf.germ ⊤ u trivial).hom) (ζ.map (U.presheaf.germ ⊤ u trivial).hom)
  have h : U.presheaf.germ ⊤ u trivial ξ.1 = U.presheaf.germ ⊤ u trivial (ζ.1 ^ (a : ZMod q).val) := by
    rw [map_pow]; exact ha
  obtain ⟨W, hW, i1, i2, he⟩ := U.presheaf.germ_eq (U := ⊤) (V := ⊤) u trivial trivial _ _ h
  refine ⟨W, a, hW, ?_⟩
  show (Scheme.Opens.ι (X := U) W).appTop.hom ξ.1 = ((Scheme.Opens.ι (X := U) W).appTop.hom ζ.1) ^ _
  rw [← map_pow, Scheme.Opens.ι_appTop]
  have hle : (Scheme.Opens.ι (X := U) W) ''ᵁ ⊤ ≤ W := by simp
  have := congrArg (U.presheaf.map (homOfLE hle).op).hom he
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp] at this
  exact (congrArg (fun k => (U.presheaf.map (Quiver.Hom.op k)).hom ξ.1) (Subsingleton.elim _ _)).trans
    (this.trans (congrArg (fun k => (U.presheaf.map (Quiver.Hom.op k)).hom (ζ.1 ^ (a : ZMod q).val)) (Subsingleton.elim _ _)))

end LateralTheory.E.AugBijPf
