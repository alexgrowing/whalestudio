import Development.EtaleCohomology.EtaleSheaves.LocallyConstantH0

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCMapPf

def TwNat : Prop := ∀ (q : ℕ) (i : ℤ) (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
  Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)

def LCSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (Y : Type)
  (φ : LocallyConstant (PrimeSpectrum B) Y) (a b : Sec F (Spec (CommRingCat.of B))),
  (∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : Y), (∀ v : V, φ (g.base v) = c) → Sec.res g a = Sec.res g b) → a = b

def LCGlue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (Y : Type)
  (φ : LocallyConstant (PrimeSpectrum B) Y) (s : Y → Sec F (Spec (CommRingCat.of B))),
  ∃ t : Sec F (Spec (CommRingCat.of B)), ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : Y),
    (∀ v : V, φ (g.base v) = c) → Sec.res g t = Sec.res g (s c)

theorem twNat : TwNat := by
  intro q i V U g ζ
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op
  have h2 := congrArg (fun k => k.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤))) h
  simp only [ModuleCat.hom_comp] at h2
  simp only [LinearMap.coe_comp] at h2
  unfold twGen ofRings.sec
  refine h2.symm.trans (congrArg ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom ?_)
  simp only [twF, Functor.comp_map]
  rw [ModuleCat.hom_ofHom]
  first
  | (erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; done)
  | (erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl)
  | exact congrArg (Submodule.Quotient.mk (p := twRel q i _)) (Finsupp.mapDomain_single (f := Prim.map g.appTop.hom) (a := ζ) (b := (1 : ULift (ZMod q))))

theorem nsmul_val {q : ℕ} [NeZero q] (i : ℤ) (U : Scheme.{0}) (x : Sec (tw q i) U) (c : ZMod q) :
    c.val • x = (ULift.up c : ULift (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift (ZMod q))]
  congr 1
  ext
  exact (ULift.down_natCast _).trans (ZMod.natCast_zmod_val c)

def sG {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B) (c : ZMod q) : Sec (tw q i) (Spec (CommRingCat.of B)) :=
  (ULift.up c : ULift (ZMod q)) • twGen i (gam ζ)

theorem res_smul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift R) (x : Sec F U) :
    Sec.res g (r • x) = r • Sec.res g x := by
  simp [Sec.res]

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := by
  simp [Sec.res]

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

def tG (hG : LCGlue) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)) :
    Sec (tw q i) (Spec (CommRingCat.of B)) :=
  Classical.choose (hG (ZMod q) (tw q i) B (ZMod q) φ (sG i ζ))

theorem tG_spec (hG : LCGlue) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B)
    (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)) (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c : ZMod q)
    (h : ∀ v : V, φ (g.base v) = c) : Sec.res g (tG hG i ζ φ) = Sec.res g (sG i ζ c) :=
  Classical.choose_spec (hG (ZMod q) (tw q i) B (ZMod q) φ (sG i ζ)) V g c h

theorem tG_add (hG : LCGlue) (hS : LCSep) {q : ℕ} (i : ℤ) {B : Type} [CommRing B] (ζ : Prim q B)
    (φ ψ : LocallyConstant (PrimeSpectrum B) (ZMod q)) : tG hG i ζ (φ + ψ) = tG hG i ζ φ + tG hG i ζ ψ := by
  let χ : LocallyConstant (PrimeSpectrum B) (ZMod q × ZMod q) :=
    ⟨fun x => (φ x, ψ x), IsLocallyConstant.comp₂ φ.2 ψ.2 Prod.mk⟩
  refine hS (ZMod q) (tw q i) B _ χ _ _ ?_
  intro V g c hc
  have h1 : ∀ v : V, φ (g.base v) = c.1 := fun v => congrArg Prod.fst (hc v)
  have h2 : ∀ v : V, ψ (g.base v) = c.2 := fun v => congrArg Prod.snd (hc v)
  have h3 : ∀ v : V, (φ + ψ) (g.base v) = c.1 + c.2 := fun v => by
    show φ (g.base v) + ψ (g.base v) = _
    rw [h1, h2]
  rw [tG_spec hG i ζ _ V g _ h3, res_add, tG_spec hG i ζ _ V g _ h1, tG_spec hG i ζ _ V g _ h2, ← res_add]
  congr 1
  unfold sG
  rw [← add_smul]
  rfl

theorem LCMap_of_parts (hT : TwNat) (hS : LCSep) (hG : LCGlue) : LCMap := by
  intro q _ i
  refine ⟨fun B _ ζ => AddMonoidHom.mk' (tG hG i ζ) (tG_add hG hS i ζ), ?_, ?_⟩
  · intro B C _ _ f ζ φ
    change Sec.res _ (tG hG i ζ φ) = tG hG i (ζ.map f) (lcMap f φ)
    refine hS (ZMod q) (tw q i) C _ (lcMap f φ) _ _ ?_
    intro V g c hc
    have hc' : ∀ v : V, φ ((g ≫ Spec.map (CommRingCat.ofHom f)).base v) = c := fun v => by
      exact hc v
    rw [← res_comp, tG_spec hG i ζ φ V _ c hc', tG_spec hG i (ζ.map f) _ V g c hc]
    unfold sG
    rw [res_smul, res_smul, hT, hT]
    have hP : Prim.map (g ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom (gam ζ) = Prim.map g.appTop.hom (gam (ζ.map f)) := by
      apply Subtype.ext
      change (g ≫ Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ζ.1) =
        g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (f ζ.1))
      have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      congr 1
      rw [← CommRingCat.comp_apply, ← hn]
      rfl
    rw [hP]
  · intro B _ ζ c
    change tG hG i ζ _ = _
    have h := tG_spec hG i ζ (LocallyConstant.const _ c) _ (𝟙 _) c (fun v => rfl)
    rw [res_id, res_id] at h
    rw [h, nsmul_val]
    rfl

def fibS (B : Type) [CommRing B] {Y : Type} (φ : LocallyConstant (PrimeSpectrum B) Y) : Sieve (Spec (CommRingCat.of B)) where
  arrows V g := ∃ c, ∀ v : V, φ (g.base v) = c
  downward_closed := by
    rintro V W g ⟨c, hc⟩ k
    exact ⟨c, fun w => hc (k.base w)⟩

theorem fibS_mem (B : Type) [CommRing B] {Y : Type} (φ : LocallyConstant (PrimeSpectrum B) Y) :
    fibS B φ ∈ Scheme.etaleTopology (Spec (CommRingCat.of B)) := by
  refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).mpr ?_
  let O : PrimeSpectrum B → (Spec (CommRingCat.of B)).Opens := fun x =>
    ⟨φ ⁻¹' {φ x}, φ.isLocallyConstant.isOpen_fiber _⟩
  refine ⟨Scheme.Cover.mkOfCovers (PrimeSpectrum B) (fun x => (O x).toScheme) (fun x => (O x).ι)
    (fun x => ⟨x, ⟨x, rfl⟩, by simp⟩), ?_⟩
  rintro _ _ ⟨x⟩
  refine ⟨φ x, fun v => ?_⟩
  have hv := v.2
  first
  | exact hv
  | (simp only [Scheme.Cover.mkOfCovers_f, Scheme.Opens.ι_apply]; exact hv)
  | (simp [O, Scheme.Cover.mkOfCovers_f] at hv ⊢; exact hv)

theorem isSheafT {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property

theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (Z : Scheme.{0}) [IsEmpty Z] (a b : Sec F Z) : a = b :=
  ((isSheafT F) _ (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext (fun _ _ h => h.elim)

theorem lcSep : LCSep := by
  intro R _ F B _ Y φ a b h
  exact ((isSheafT F) _ (fibS_mem B φ)).isSeparatedFor.ext (fun V g hg => h V g hg.choose hg.choose_spec)

theorem lcGlue : LCGlue := by
  intro R _ F B _ Y φ s
  let x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) (fibS B φ).arrows :=
    fun V g hg => Sec.res g (s hg.choose)
  have key : ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of B)) (c d : Y), (∀ v : V, φ (g.base v) = c) →
      (∀ v : V, φ (g.base v) = d) → Sec.res g (s c) = Sec.res g (s d) := by
    intro V g c d hc hd
    by_cases hV : Nonempty V
    · obtain ⟨v⟩ := hV
      rw [← hc v, ← hd v]
    · have : IsEmpty V := not_nonempty_iff.1 hV
      exact sec_empty F V _ _
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    change Sec.res (k ≫ g) (s _) = Sec.res k (Sec.res g (s _))
    rw [← res_comp]
    exact key W (k ≫ g) _ _ ((fibS B φ).downward_closed hg k).choose_spec (fun w => hg.choose_spec (k.base w))
  obtain ⟨t, ht, -⟩ := (isSheafT F) _ (fibS_mem B φ) x hx
  refine ⟨t, fun V g c hc => ?_⟩
  have h1 := ht g ⟨c, hc⟩
  refine h1.trans (key V g _ _ (Exists.choose_spec (p := fun c => ∀ v : V, φ (g.base v) = c) ⟨c, hc⟩) hc)

theorem LCMap_of : LCMap := LCMap_of_parts twNat lcSep lcGlue

end LateralTheory.E.LCMapPf
