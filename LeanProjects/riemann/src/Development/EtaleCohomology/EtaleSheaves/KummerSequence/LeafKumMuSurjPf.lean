import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuUnitsPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf

namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf

def LeafKumMuSurjLoc : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∀ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, Gen q κ →
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) →
      ∀ s : Sec Gm U, Sec.map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q) s = 0 →
        ∃ S ∈ Scheme.etaleTopology U, ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), S f → ∃ t, Sec.map κ t = Sec.res f s

def LeafKumMuSurjInj : Prop := LeafKumMuInj

theorem sec_res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res f x) = Sec.res (g ≫ f) x := by
  have h := congrArg (fun m => ModuleCat.Hom.hom m x) (F.obj.map_comp f.op g.op)
  exact h.symm

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (κ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map κ (Sec.res g x) = Sec.res g (Sec.map κ x) := by
  have h := congrArg (fun m => ModuleCat.Hom.hom m x) (κ.hom.naturality g.op)
  exact h

theorem isSheaf_types {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget _)).1 F.property)

theorem sec_ext {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (a b : Sec F U) (h : ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), S f → Sec.res f a = Sec.res f b) : a = b :=
  ((isSheaf_types F) S hS).isSeparatedFor.ext (fun _ f hf => h f hf)

theorem sec_glue {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (t : ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), S f → Sec F V)
    (ht : ∀ ⦃W V : Scheme.{0}⦄ (g : W ⟶ V) (f : V ⟶ U) (hf : S f), t (g ≫ f) (S.downward_closed hf g) = Sec.res g (t f hf)) :
    ∃ a : Sec F U, ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U) (hf : S f), Sec.res f a = t f hf := by
  let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) S.arrows := fun _ f hf => t f hf
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W f g hf
    exact ht g f hf
  exact ⟨((isSheaf_types F) S hS).amalgamate x hx, fun V f hf => ((isSheaf_types F) S hS).valid_glue hx f hf⟩

def LeafKumMuSurjUnit : Prop := ∀ (q : ℕ) (U : Scheme.{0}) (s : Sec Gm U),
  Sec.map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q) s = 0 →
    ∃ S ∈ Scheme.etaleTopology U, ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), S f →
      ∃ u : (Γ(V, ⊤))ˣ, u ^ q = 1 ∧ Sec.res f s = (ofRings.sec unitsF V ⟨Additive.ofMul u⟩ : Sec Gm V)

def LeafKumMuSurjRoot : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∀ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, Gen q κ →
    ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) → ∀ u : (Γ(U, ⊤))ˣ, u ^ q = 1 →
      ∃ S ∈ Scheme.etaleTopology U, ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), S f →
        ∃ t, Sec.map κ t = Sec.res f (ofRings.sec unitsF U ⟨Additive.ofMul u⟩ : Sec Gm U)

theorem LeafKumMuSurjLoc_of (hU' : LeafKumMuSurjUnit) (hR : LeafKumMuSurjRoot) : LeafKumMuSurjLoc := by
  intro q _ B _ hq κ hg U hU s hs
  obtain ⟨S, hS, h1⟩ := hU' q U s hs
  choose u hu1 hu2 using h1
  have hsub : ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), Nonempty (Sx (sp B) 0 V) := fun V f =>
    ⟨((sp B).obj (op (SimplexCategory.mk 0))).map f.op hU.some⟩
  choose R hR1 hR2 using fun ⦃V : Scheme.{0}⦄ (f : V ⟶ U) (hf : S f) =>
    hR q B hq κ hg V (hsub f) (u f hf) (hu1 f hf)
  refine ⟨Sieve.bind S.arrows R, Scheme.etaleTopology.bind_covering hS hR1, ?_⟩
  rintro W h ⟨V, g, f, hf, hg', rfl⟩
  obtain ⟨t, ht⟩ := hR2 f hf g hg'
  exact ⟨t, by rw [ht, ← hu2 f hf]; exact sec_res_comp Gm g f s⟩

theorem LeafKumMuSurj_of (hL : LeafKumMuSurjLoc) (hI : LeafKumMuSurjInj) : LeafKumMuSurj := by
  intro q _ B _ hq κ hg U hU s hs
  obtain ⟨S, hS, hloc⟩ := hL q B hq κ hg U hU s hs
  choose t ht using hloc
  have hsub : ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), Nonempty (Sx (sp B) 0 V) := fun V f =>
    ⟨((sp B).obj (op (SimplexCategory.mk 0))).map f.op hU.some⟩
  obtain ⟨a, ha⟩ := sec_glue _ S hS (fun V f hf => t f hf) (by
    intro W V g f hf
    apply hI q B hq κ hg W (hsub (g ≫ f))
    rw [ht, sec_map_res, ht, sec_res_comp])
  refine ⟨a, sec_ext Gm S hS _ _ (fun V f hf => ?_)⟩
  rw [← sec_map_res, ha f hf, ht f hf]

theorem LeafKumMuSurjUnit_pf : LeafKumMuSurjUnit := by
  intro q U s hs
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ) := Scheme.Γ ⋙ unitsF
  let η := toSheafify Scheme.etaleTopology P
  let pw : P ⟶ P := Functor.whiskerLeft Scheme.Γ (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powNat q)
  have hsurj : Presheaf.IsLocallySurjective Scheme.etaleTopology η := inferInstance
  have hinj : Presheaf.IsLocallyInjective Scheme.etaleTopology η := inferInstance
  have hS1 : Presheaf.imageSieve η s ∈ Scheme.etaleTopology U := Presheaf.imageSieve_mem Scheme.etaleTopology η (U := op U) s
  have hnat : ∀ {V : Scheme.{0}} (x : P.obj (op V)),
      (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom.app (op V) (η.app (op V) x) = η.app (op V) (pw.app (op V) x) := by
    intro V x
    have h := congrArg (fun m => m.app (op V) x) (toSheafify_naturality Scheme.etaleTopology pw)
    exact h.symm
  have hx : ∀ {V : Scheme.{0}} (f : V ⟶ U) (hf : Presheaf.imageSieve η s f),
      η.app (op V) (pw.app (op V) (Presheaf.localPreimage η s f hf)) = η.app (op V) 0 := by
    intro V f hf
    have h3 : η.app (op V) (Presheaf.localPreimage η s f hf) = Sec.res f s := Presheaf.app_localPreimage η s f hf
    rw [← hnat, h3, map_zero]
    exact (sec_map_res (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q) f s).trans (by rw [hs]; exact map_zero _)
  refine ⟨Sieve.bind (Presheaf.imageSieve η s).arrows
    (fun V f hf => Presheaf.equalizerSieve (F := P) (X := op V) (pw.app (op V) (Presheaf.localPreimage η s f hf)) 0),
    Scheme.etaleTopology.bind_covering hS1 (fun V f hf => Presheaf.equalizerSieve_mem Scheme.etaleTopology η _ _ (hx f hf)), ?_⟩
  rintro W h ⟨V, g, f, hf, hg, rfl⟩
  let x := Presheaf.localPreimage η s f hf
  refine ⟨(P.map g.op x).down.toMul, ?_, ?_⟩
  · have h1 : P.map g.op (pw.app (op V) x) = P.map g.op 0 := hg
    rw [map_zero, ← NatTrans.naturality_apply] at h1
    have h2 := congrArg (fun y => Additive.toMul y.down) h1
    have h4 : Additive.toMul (q • (P.map g.op x).down) = 1 := h2
    rwa [toMul_nsmul] at h4
  · have h3 : η.app (op V) x = Sec.res f s := Presheaf.app_localPreimage η s f hf
    rw [← sec_res_comp Gm g f s, ← h3]
    exact (NatTrans.naturality_apply η g.op x).symm

theorem LeafKumMuSurj_of'' (hU' : LeafKumMuSurjUnit) (hR : LeafKumMuSurjRoot) (hI : LeafKumMuSurjInj) : LeafKumMuSurj :=
  LeafKumMuSurj_of (LeafKumMuSurjLoc_of hU' hR) hI

def LeafKumMuSurjPrim : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∀ U : Scheme.{0}, Nonempty (Sx (sp B) 0 U) →
    ∃ S ∈ Scheme.etaleTopology U, ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), S f → Nonempty (Prim q Γ(V, ⊤))

def LeafKumMuSurjPow : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), u ^ q = 1 →
  ∃ S ∈ Scheme.etaleTopology U, ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), S f →
    ∃ a : ℕ, (Scheme.Γ.map f.op).hom (u : Γ(U, ⊤)) = ((Scheme.Γ.map f.op).hom ζ.1) ^ a

theorem prim_pow_q {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h
  exact sub_eq_zero.1 h

theorem secUnits_res {U V : Scheme.{0}} (f : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res f (ofRings.sec unitsF U ⟨Additive.ofMul u⟩ : Sec Gm U) =
      (ofRings.sec unitsF V ⟨Additive.ofMul (Units.map (Scheme.Γ.map f.op).hom.toMonoidHom u)⟩ : Sec Gm V) :=
  (NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) f.op _).symm

theorem LeafKumMuSurjRoot_of (hP : LeafKumMuSurjPrim) (hW : LeafKumMuSurjPow) : LeafKumMuSurjRoot := by
  intro q _ B _ hq κ hg U hU u hu
  obtain ⟨S, hS, hS'⟩ := hP q B hq U hU
  have key : ∀ ⦃V : Scheme.{0}⦄ (f : V ⟶ U), S f → ∃ R ∈ Scheme.etaleTopology V, ∀ ⦃W : Scheme.{0}⦄ (g : W ⟶ V), R g →
      ∃ t, Sec.map κ t = Sec.res (g ≫ f) (ofRings.sec unitsF U ⟨Additive.ofMul u⟩ : Sec Gm U) := by
    intro V f hf
    obtain ⟨ζ⟩ := hS' f hf
    let uV := Units.map (Scheme.Γ.map f.op).hom.toMonoidHom u
    have huV : uV ^ q = 1 := by
      rw [show uV ^ q = Units.map (Scheme.Γ.map f.op).hom.toMonoidHom (u ^ q) from (map_pow _ u q).symm, hu]
      exact map_one _
    obtain ⟨R, hR, hR'⟩ := hW q V ζ uV huV
    refine ⟨R, hR, fun W g hgR => ?_⟩
    obtain ⟨a, ha⟩ := hR' g hgR
    let ζW := Prim.map (Scheme.Γ.map g.op).hom ζ
    have hζu : IsUnit ζW.1 := IsUnit.of_pow_eq_one (prim_pow_q ζW) (NeZero.ne q)
    have hgen := hg W ζW hζu.unit rfl
    refine ⟨a • (twGen 1 ζW : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) W), ?_⟩
    have e1 : Sec.map κ (a • (twGen 1 ζW : Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) W)) =
        a • Sec.map κ (twGen 1 ζW) := map_nsmul (κ.hom.app (op W)).hom a _
    rw [e1, hgen]
    refine Eq.trans ?_ (secUnits_res (g ≫ f) u).symm
    have e2 : a • (ofRings.sec unitsF W ⟨Additive.ofMul hζu.unit⟩ : Sec Gm W) =
        ofRings.sec unitsF W (a • (⟨Additive.ofMul hζu.unit⟩ : ULift.{1} (Additive (Γ(W, ⊤))ˣ))) :=
      (map_nsmul ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op W)).hom a _).symm
    refine e2.trans ?_
    congr 1
    apply ULift.ext
    show a • Additive.ofMul hζu.unit = _
    rw [← ofMul_pow]
    congr 1
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.coe_map, MonoidHom.coe_coe]
    show ((Scheme.Γ.map g.op).hom ζ.1) ^ a = _
    rw [← ha]
    simp [uV, op_comp]
    rfl
  choose R hR1 hR2 using key
  refine ⟨Sieve.bind S.arrows R, Scheme.etaleTopology.bind_covering hS hR1, ?_⟩
  rintro W h ⟨V, g, f, hf, hgR, rfl⟩
  exact hR2 f hf g hgR

theorem LeafKumMuSurj_of' (hR : LeafKumMuSurjRoot) (hI : LeafKumMuSurjInj) : LeafKumMuSurj :=
  LeafKumMuSurj_of'' LeafKumMuSurjUnit_pf hR hI

theorem etale_mu_twist_sections_surj_of_prim_root_pow_inj (hP : LeafKumMuSurjPrim) (hW : LeafKumMuSurjPow) (hI : LeafKumMuSurjInj) : LeafKumMuSurj :=
  LeafKumMuSurj_of' (LeafKumMuSurjRoot_of hP hW) hI

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf
