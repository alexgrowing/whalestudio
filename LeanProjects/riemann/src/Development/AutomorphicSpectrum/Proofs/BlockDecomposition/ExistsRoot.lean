import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FKum

variable {l : ℕ} [Fact l.Prime]

def tu (A : PAlg l) : A.A →* Γ(SU A, ⊤) :=
  ((toΓ A.Ug).toMonoidHom.comp (algebraMap A.U A.Ug).toMonoidHom).comp A.sharp

theorem tu_apply (A : PAlg l) (a : A.A) : tu A a = toΓ A.Ug (algebraMap A.U A.Ug (A.sharp a)) := rfl

theorem sharp_nat {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    PAlg.mapU f (A.sharp a) = B.sharp (PAlg.Hom.f f a) := by
  change PAlg.mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (PAlg.Hom.f f a))
  rw [PAlg.mapU_th]
  exact congrArg B.th (WittVector.map_teichmuller _ _ _)

theorem tu_nat {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    (Spec.map (CommRingCat.ofHom (PAlg.mapUg f))).appTop.hom (tu A a) = tu B (PAlg.Hom.f f a) := by
  rw [tu_apply, toΓ_nat, PAlg.mapUg_algebraMap, sharp_nat]; rfl

theorem u_congr {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha hb; rfl

theorem toΓ_hom (B : Type) [CommRing B] (x : Γ(Spec (CommRingCat.of B), ⊤)) :
    toΓ B ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x) = x :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of B)).hom_inv_id x

abbrev gU (B : PAlg l) : SU B ⟶ Spec (CommRingCat.of B.U) := Spec.map (CommRingCat.ofHom (algebraMap B.U B.Ug))

theorem tu_of_sharp {X : Scheme.{0}} (D : LineData X) (B : PAlg l) (a b : Spec (CommRingCat.of B.U) ⟶ D.Y)
    (h : a ≫ D.f = b ≫ D.f) (w : B.A)
    (hw : B.sharp w = (Scheme.ΓSpecIso (CommRingCat.of B.U)).hom.hom (D.u a b h).val)
    (h' : (gU B ≫ a) ≫ D.f = (gU B ≫ b) ≫ D.f) :
    tu B w = (D.u (gU B ≫ a) (gU B ≫ b) h').val := by
  rw [D.nat (gU B) a b h, tu_apply, hw, ← toΓ_nat, toΓ_hom]
  rfl

theorem exists_root (A : PAlg l) (n : ℕ) (w : (A.A)ˣ) : ∃ ω : (A.A)ˣ, ω ^ l ^ n = w := by
  have hs : ∀ (n : ℕ) (x : A.A), ∃ y : A.A, y ^ l ^ n = x := by
    intro n
    induction n with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := A.A) (p := l)).2 x
      obtain ⟨z, hz⟩ := ih y
      exact ⟨z, by rw [pow_succ, pow_mul, hz]; exact hy⟩
  obtain ⟨y, hy⟩ := hs n w
  have hu : IsUnit y := (isUnit_pow_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 (hy ▸ w.isUnit)
  obtain ⟨ω, rfl⟩ := hu
  exact ⟨ω, Units.ext (by simpa using hy)⟩

section Main
variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : Model l K} {C : Type 1} [Category.{0} C]

abbrev Ao (G : C ⥤ El M.P) (c : C) : PAlg l := (G.obj c).1.obj

abbrev mp (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : Ao G c ⟶ Ao G c' := (G.map φ).1.hom

abbrev sg (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : SU (Ao G c') ⟶ SU (Ao G c) :=
  Spec.map (CommRingCat.ofHom (PAlg.mapUg (mp G φ)))

abbrev sgU (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') :
    Spec (CommRingCat.of (Ao G c').U) ⟶ Spec (CommRingCat.of (Ao G c).U) :=
  Spec.map (CommRingCat.ofHom (PAlg.mapU (mp G φ)))

theorem sg_gU (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : sg G φ ≫ gU (Ao G c) = gU (Ao G c') ≫ sgU G φ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun x => PAlg.mapUg_algebraMap _ x

theorem sg_comp (G : C ⥤ El M.P) {c c' c'' : C} (φ : c ⟶ c') (ψ : c' ⟶ c'') :
    sg G (φ ≫ ψ) = sg G ψ ≫ sg G φ := by
  have e : mp G (φ ≫ ψ) = mp G φ ≫ mp G ψ := congrArg (fun t => t.1.hom) (G.map_comp φ ψ)
  rw [sg, e]
  exact (congrArg Spec.map ((UgR l).map_comp _ _)).trans (Spec.map_comp _ _)

theorem sgU_pt (G : C ⥤ El M.P) {c c' : C} (φ : c ⟶ c') : sgU G φ ≫ (G.obj c).2.1 = (G.obj c').2.1 :=
  congrArg Subtype.val (G.map φ).2

variable {D : LineData M.X} {D' : LineData (gb M)} {π : D'.Y ⟶ D.Y} {G : C ⥤ El M.P}

theorem hr_eq (hBC : D.IsBC (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) D' π) (Λ : Lift G D)
    (p' : ∀ c, SU (Ao G c) ⟶ D'.Y) (hπ : ∀ c, p' c ≫ π = gU (Ao G c) ≫ Λ.p c) {c c' : C} (φ : c ⟶ c')
    (h : (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f) :
    tu (Ao G c') (Λ.w φ).val = (D'.u (sg G φ ≫ p' c) (p' c') h).val := by
  have h0 : (sgU G φ ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [Category.assoc, Λ.hp, Λ.hp, sgU_pt]
  have h1 : (gU (Ao G c') ≫ sgU G φ ≫ Λ.p c) ≫ D.f = (gU (Ao G c') ≫ Λ.p c') ≫ D.f := by
    rw [Category.assoc, Category.assoc, ← Category.assoc (sgU G φ), h0, Category.assoc]
  have h2 : ((sg G φ ≫ p' c) ≫ π) ≫ D.f = (p' c' ≫ π) ≫ D.f := by
    have key : ∀ {V : Scheme.{0}} (t : V ⟶ D'.Y), (t ≫ π) ≫ D.f =
        (t ≫ D'.f) ≫ (pullback.fst _ _ ≫ pullback.fst _ _ : gb M ⟶ M.X) := fun t => by
      rw [Category.assoc, hBC.1, Category.assoc]
    rw [key, key, h]
  rw [tu_of_sharp D _ _ _ h0 _ (Λ.hw φ h0) h1, hBC.2.2 _ _ _ h h2]
  refine congrArg Units.val (u_congr D ?_ (hπ c').symm _ _)
  rw [Category.assoc, hπ, ← Category.assoc, ← sg_gU, Category.assoc]

abbrev tuU (A : PAlg l) : (A.A)ˣ →* (Γ(SU A, ⊤))ˣ := Units.map (tu A)

abbrev chU {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) : ((Ao G c₂).A)ˣ :=
  Units.map (PAlg.Hom.f (mp G ψ)).toMonoidHom a * b * c⁻¹

theorem map_tuU {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) :
    Units.map (sg G ψ).appTop.hom.toMonoidHom (tuU (Ao G c₁) a) =
      tuU (Ao G c₂) (Units.map (PAlg.Hom.f (mp G ψ)).toMonoidHom a) :=
  Units.ext (tu_nat (mp G ψ) a.val)

theorem chain_val {c₁ c₂ : C} (G : C ⥤ El M.P) (ψ : c₁ ⟶ c₂) (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) :
    Units.map (sg G ψ).appTop.hom.toMonoidHom (tuU (Ao G c₁) a) * tuU (Ao G c₂) b * (tuU (Ao G c₂) c)⁻¹ =
      tuU (Ao G c₂) (chU G ψ a b c) := by
  rw [map_tuU, chU, map_mul, map_mul, map_inv]

theorem chain_pow {c₀ c₁ c₂ : C} (p' : ∀ c, SU (Ao G c) ⟶ D'.Y) (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂)
    (hχ : φ ≫ ψ = χ) (q : ℕ) (a : (Γ(SU (Ao G c₁), ⊤))ˣ) (b c : (Γ(SU (Ao G c₂), ⊤))ˣ)
    (h₁ : (sg G φ ≫ p' c₀) ≫ D'.f = p' c₁ ≫ D'.f) (h₂ : (sg G ψ ≫ p' c₁) ≫ D'.f = p' c₂ ≫ D'.f)
    (h₃ : (sg G χ ≫ p' c₀) ≫ D'.f = p' c₂ ≫ D'.f)
    (ha : a ^ q = D'.u (sg G φ ≫ p' c₀) (p' c₁) h₁) (hb : b ^ q = D'.u (sg G ψ ≫ p' c₁) (p' c₂) h₂)
    (hc : c ^ q = D'.u (sg G χ ≫ p' c₀) (p' c₂) h₃) :
    (Units.map (sg G ψ).appTop.hom.toMonoidHom a * b * c⁻¹) ^ q = 1 := by
  have h₄ : (sg G ψ ≫ sg G φ ≫ p' c₀) ≫ D'.f = (sg G ψ ≫ p' c₁) ≫ D'.f := by
    rw [Category.assoc, h₁, Category.assoc]
  rw [mul_pow, mul_pow, inv_pow, ← map_pow, ha, hb, hc, ← D'.nat (sg G ψ) _ _ h₁, D'.coc _ _ _ h₄ h₂]
  rw [u_congr D' (a' := sg G χ ≫ p' c₀) (b' := p' c₂) _ rfl _ h₃, mul_inv_cancel]
  rw [← hχ, sg_comp, Category.assoc]

abbrev tuP (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) (c : C) :
    ((Ao G c).A)ˣ →* (Γ((probe H r (G ⋙ CategoryOfElements.π _) n).U c, ⊤))ˣ := tuU (Ao G c)

theorem chain_valP (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) {c₁ c₂ : C} (ψ : c₁ ⟶ c₂)
    (a : ((Ao G c₁).A)ˣ) (b c : ((Ao G c₂).A)ˣ) :
    Units.map ((probe H r (G ⋙ CategoryOfElements.π _) n).S.map ψ).unop.appTop.hom.toMonoidHom (tuP H r G n c₁ a) *
      tuP H r G n c₂ b * (tuP H r G n c₂ c)⁻¹ = tuP H r G n c₂ (chU G ψ a b c) :=
  chain_val G ψ a b c

theorem pow_field (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ) (c : C)
    (f : LocallyConstant (SU (Ao G c)) (ZMod (l ^ n))) (u : ((Ao G c).A)ˣ)
    (h : IsPow (r.zeta (Ao G c) n) f (tu (Ao G c) u.val)) :
    IsPow ((probe H r (G ⋙ CategoryOfElements.π _) n).ζ c) f (tuP H r G n c u).val := h

theorem kum_of (H : RIn l) (r : Roots l) (G : C ⥤ El M.P) (n : ℕ)
    (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2) (p' : ∀ c, SU (Ao G c) ⟶ D'.Y)
    (hf : ∀ c, p' c ≫ D'.f = geomPt M (Ao G c) (G.obj c).2) (ω : ∀ (c c' : C), (c ⟶ c') → ((Ao G c').A)ˣ)
    (hfh : ∀ {c c' : C} (φ : c ⟶ c'), (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f)
    (hr : ∀ {c c' : C} (φ : c ⟶ c'), tuU (Ao G c') (ω c c' φ) ^ l ^ n = D'.u (sg G φ ≫ p' c) (p' c') (hfh φ))
    (hz : ∀ s : ComposableArrows C 2, IsPow ((probe H r (G ⋙ CategoryOfElements.π _) n).ζ (s.obj (Fin.last 2))) (z s)
      (tuP H r G n (s.obj (Fin.last 2)) (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2)))).val) :
    Nonempty (IsKumCoc (pts H r M G n) D' z) :=
  ⟨{ p := p'
     hp := hf
     r := fun {c c'} φ => tuP H r G n c' (ω c c' φ)
     hr := fun φ => hr φ
     hz := fun s => by
       rw [chain_valP]
       exact hz s }⟩

theorem log_of (hN : LcNat) (H : RIn l) (r : Roots l) {D : LineData M.X} (G : C ⥤ El M.P) (n : ℕ) (Λ : Lift G D)
    (z : Cn (probe H r (G ⋙ CategoryOfElements.π _) n).L 2)
    (h : ∀ s : ComposableArrows C 2, IsLog (Ao G (s.obj (Fin.last 2))) n (tei (Ao G (s.obj (Fin.last 2))) (Λ.r s))
      ((ACris.periodT (untilt_epsilon (p := l)) : Acris l) • lcA (Ao G (s.obj (Fin.last 2))) n (z s))) :
    Λ.IsCoc n (tCo G n 2 (lcCo hN H r G n 2 z)) := h

theorem r_eq {D : LineData M.X} (Λ : Lift G D) (n : ℕ) (ω : ∀ (c c' : C), (c ⟶ c') → ((Ao G c').A)ˣ)
    (hω : ∀ (c c' : C) (φ : c ⟶ c'), ω c c' φ ^ l ^ n = Λ.w φ) (s : ComposableArrows C 2) :
    Λ.r s = (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2))) ^ l ^ n := by
  rw [chU, mul_pow, mul_pow, inv_pow, ← map_pow, hω, hω, hω]
  rfl

end Main

theorem fKum (hR : RootPow) (hL : LcLog) : FKum := by
  intro hN l _ H r K M D D' π hBC C _ G Λ n
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hb : ∀ c, ∃ b : SU (Ao G c) ⟶ D'.Y, b ≫ π = gU (Ao G c) ≫ Λ.p c ∧
      b ≫ D'.f = geomPt M (Ao G c) (G.obj c).2 := fun c =>
    hBC.2.1 _ _ _ (by rw [Category.assoc, Λ.hp, geomPt_fst])
  choose p' hπ hf using hb
  have hω : ∀ (c c' : C) (φ : c ⟶ c'), ∃ ω : ((Ao G c').A)ˣ, ω ^ l ^ n = Λ.w φ := fun c c' φ => exists_root _ n _
  choose ω hω using hω
  have hfh : ∀ {c c' : C} (φ : c ⟶ c'), (sg G φ ≫ p' c) ≫ D'.f = p' c' ≫ D'.f := by
    intro c c' φ
    rw [Category.assoc, hf, hf]
    exact (pts H r M G n).nat φ
  have hr : ∀ {c c' : C} (φ : c ⟶ c'), tuU (Ao G c') (ω c c' φ) ^ l ^ n = D'.u (sg G φ ≫ p' c) (p' c') (hfh φ) := by
    intro c c' φ
    rw [← map_pow, hω c c' φ]
    exact Units.ext (hr_eq hBC Λ p' hπ φ _)
  have hz : ∀ s : ComposableArrows C 2, ∃ f : LocallyConstant (SU (Ao G (s.obj (Fin.last 2)))) (ZMod (l ^ n)),
      IsPow (r.zeta (Ao G (s.obj (Fin.last 2))) n) f
        (tu (Ao G (s.obj (Fin.last 2))) (chU G (s.map' 1 2) (ω _ _ (s.map' 0 1)) (ω _ _ (s.map' 1 2)) (ω _ _ (s.map' 0 2))).val) := by
    intro s
    refine (hR (l ^ n) _ _).1 _ ?_
    have h := chain_pow p' (s.map' 0 1) (s.map' 1 2) (s.map' 0 2) (by rw [← s.map_comp]; rfl) (l ^ n)
      (tuU _ (ω _ _ (s.map' 0 1))) (tuU _ (ω _ _ (s.map' 1 2))) (tuU _ (ω _ _ (s.map' 0 2)))
      (hfh _) (hfh _) (hfh _) (hr _) (hr _) (hr _)
    rw [chain_val] at h
    exact congrArg Units.val h
  choose z hz using hz
  refine ⟨z, kum_of H r G n z p' hf ω hfh hr fun s => pow_field H r G n _ _ _ (hz s), log_of hN H r G n Λ z fun s => ?_⟩
  have h := hL l H r (Ao G (s.obj (Fin.last 2))) (G.obj (s.obj (Fin.last 2))).1.property n _ (z s) (hz s)
  rw [← Units.val_pow_eq_pow_val, ← r_eq Λ n ω hω s] at h
  exact h

end GlobalTheory.CompanionTheory.FKum
