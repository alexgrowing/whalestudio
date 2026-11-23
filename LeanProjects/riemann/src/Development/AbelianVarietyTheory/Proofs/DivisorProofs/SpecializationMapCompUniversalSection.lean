import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStableOfNoBoundary

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.GalCarry

attribute [local instance] Over.cartesianMonoidalCategory

section Adelic

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y Y' : Var F}

def DivIso (Δ : Y.Dv) (Δ' : Y'.Dv) (φ : Y.X ≅ Y'.X) (ψ : Y'.Fn →+* Y.Fn) (u : Y.Fnˣ) : Prop :=
  φ.hom ≫ Y'.str = Y.str ∧ genericPt Y ≫ φ.hom = spMap ψ ≫ genericPt Y' ∧ Y.dim = Y'.dim ∧
    ∀ (y : Y.X) (g : Y'.Fnˣ), Δ'.IsEqn (φ.hom y) g → Δ.IsEqn y (Units.map (ψ : Y'.Fn →* Y.Fn) g * u)

def AdlIso (A : Adl C Y) (A' : Adl C Y') (φ : Y.X ≅ Y'.X) (ψ : Y'.Fn →+* Y.Fn) (u : Y.Fnˣ) : Prop :=
  DivIso A.D A'.D φ ψ u ∧ A.n = A'.n ∧ A.ci = A'.ci ∧
    (∀ (σ : F →+* ℂ) (p : Pts Y σ) (p' : Pts Y' σ), p'.1 = p.1 ≫ φ.hom → ∀ g : Y'.Fnˣ, A'.D.IsEqn (under p') g →
      C.pn Y σ A.D (A.m σ) (C.cx Y σ ((Units.map (ψ : Y'.Fn →* Y.Fn) g * u)⁻¹ : Y.Fnˣ)) p =
        C.pn Y' σ A'.D (A'.m σ) (C.cx Y' σ (g⁻¹ : Y'.Fnˣ)) p') ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y) (y' : AlgPt Y'), y'.1 = y.1 ≫ φ.hom →
      A.lg v ε y = A'.lg v ε y' + Real.log (ε.w (valAt y.1
        ((Units.map (ψ : Y'.Fn →* Y.Fn) (eqn A'.D (below y'.1)) * u * (eqn A.D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn)))

omit [NumberField F] in

theorem spMap_alg_stalkPt (y : Y.X) :
    spMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) ≫ stalkPt Y y = genericPt Y :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

omit [NumberField F] in

theorem map_alg {f : Y.X ⟶ Y'.X} {ψ : Y'.Fn →+* Y.Fn} (h : genericPt Y ≫ f = spMap ψ ≫ genericPt Y') (y : Y.X)
    (z : Y'.X.presheaf.stalk (f y)) : ψ (algebraMap (Y'.X.presheaf.stalk (f y)) Y'.X.functionField z) =
      algebraMap (Y.X.presheaf.stalk y) Y.X.functionField ((f.stalkMap y).hom z) := by
  have h1 : spMap (f.stalkMap y).hom ≫ stalkPt Y' (f y) = stalkPt Y y ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have h2 : spMap (ψ.comp (algebraMap (Y'.X.presheaf.stalk (f y)) Y'.X.functionField)) =
      spMap ((algebraMap (Y.X.presheaf.stalk y) Y.X.functionField).comp (f.stalkMap y).hom) :=
    (cancel_mono (Y'.X.fromSpecStalk (f y))).1 (by
      have e1 := Spec.map_comp (CommRingCat.ofHom (algebraMap (Y'.X.presheaf.stalk (f y)) Y'.X.functionField))
        (CommRingCat.ofHom ψ)
      have e2 := Spec.map_comp (CommRingCat.ofHom (f.stalkMap y).hom)
        (CommRingCat.ofHom (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField))
      refine (congrArg (· ≫ _) e1).trans (Eq.trans ?_ (congrArg (· ≫ _) e2).symm)
      exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (spMap_alg_stalkPt (f y))).trans <| h.symm.trans <|
        (congrArg (· ≫ f) (spMap_alg_stalkPt y).symm).trans <| (Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) h1.symm).trans (Category.assoc _ _ _).symm)
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective h2)) z

omit [NumberField F] in

theorem regAt_map {f : Y.X ⟶ Y'.X} {ψ : Y'.Fn →+* Y.Fn} (h : genericPt Y ≫ f = spMap ψ ≫ genericPt Y') {y : Y.X}
    {a : Y'.Fn} (ha : RegAt (f y) a) : RegAt y (ψ a) := by
  obtain ⟨z, rfl⟩ := ha
  exact ⟨_, (map_alg h y z).symm⟩

omit [NumberField F] in

theorem unitAt_map {f : Y.X ⟶ Y'.X} {ψ : Y'.Fn →+* Y.Fn} (h : genericPt Y ≫ f = spMap ψ ≫ genericPt Y') {y : Y.X}
    {a : Y'.Fn} (ha : UnitAt (f y) a) : UnitAt y (ψ a) := by
  obtain ⟨z, hz, rfl⟩ := ha
  exact ⟨_, hz.map _, (map_alg h y z).symm⟩

omit [NumberField F] in

theorem valAt_map {f : Y.X ⟶ Y'.X} {ψ : Y'.Fn →+* Y.Fn} (h : genericPt Y ≫ f = spMap ψ ≫ genericPt Y') {K : Type}
    [Field K] (p : Sp K ⟶ Y.X) {a : Y'.Fn} (ha : RegAt (below (p ≫ f)) a) : valAt p (ψ a) = valAt (p ≫ f) a := by
  obtain ⟨z, rfl⟩ := ha
  rw [Base.valAt_stalk]
  refine (congrArg _ (map_alg h (below p) z)).trans ((Base.valAt_stalk _ _).trans ?_)
  rw [Scheme.stalkClosedPointTo_comp]
  rfl

end Adelic

def CorrSt : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (I I' : Type) (Y : I → Var F) (Y' : I' → Var F)
    (Rel : ∀ (K : Type) [Field K] (i : I) (i' : I'), (Sp K ⟶ (Y i).X) → (Sp K ⟶ (Y' i').X) → Prop),
    (∀ (K : Type) [Field K] i i' p p', Rel K i i' p p' → p' ≫ (Y' i').str = p ≫ (Y i).str) →
    (∀ (K K' : Type) [Field K] [Field K'] (ν : K →+* K') i i' p p', Rel K i i' p p' →
      Rel K' i i' (spMap ν ≫ p) (spMap ν ≫ p')) →
    (∀ (K : Type) [Field K] [IsAlgClosed K] i p, ∃! q : Σ i', (Sp K ⟶ (Y' i').X), Rel K i q.1 p q.2) →
    (∀ (K : Type) [Field K] [IsAlgClosed K] i' p', ∃! q : Σ i, (Sp K ⟶ (Y i).X), Rel K q.1 i' q.2 p') →
    (∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (L : Type) [Field L] (ν : V →+* L) (k : Type) [Field k]
      (r : V →+* k) i i' (q : Sp V ⟶ (Y i).X) (q' : Sp V ⟶ (Y' i').X), Function.Injective ν →
      RingHom.ker r = IsLocalRing.maximalIdeal V → Rel L i i' (spMap ν ≫ q) (spMap ν ≫ q') →
      Rel k i i' (spMap r ≫ q) (spMap r ≫ q')) →
    ∃ e : I ≃ I', ∀ i, ∃ φ : (Y i).X ≅ (Y' (e i)).X,
      ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ (Y i).X), Rel K i (e i) p (p ≫ φ.hom)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure Tw (Z : Model Xo c β) : Type where

  s : E ≃ₐ[ℚ] E

  σ : 𝓞 E ≃+* 𝓞 E
  coe_σ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = s a
  w0 : σ H.w0 = H.w0

  r : Xo.XF c ≅ Xo.XF c
  r_snd : r.hom ≫ pullback.snd _ _ = pullback.snd _ _

  ν : TwMap σ Z.oF.t Z.oF.t r.hom

  ρ : Z.X ≅ Z.X

  mu : TwMap σ Z.t Z.t ρ.hom
  specializationMap_comp_universalSection : ρ.hom ≫ Z.s = Z.s
  j_ρ : Z.j ≫ ρ.hom = r.hom ≫ Z.j
  m_mu : Z.m.φ ≫ mu.cm.F = ν.cm.F ≫ Z.m.φ

theorem exists_tw {Y : Model Xo c β} {T : TorModel Y} (h : IsStable T) (s : E ≃ₐ[ℚ] E) (σ : 𝓞 E ≃+* 𝓞 E)
    (hs : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = s a) (hw : σ H.w0 = H.w0) (r : Xo.XF c ≅ Xo.XF c)
    (ν : TwMap σ T.Z.oF.t T.Z.oF.t r.hom) (hr : r.hom ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ τ : Tw T.Z, τ.s = s := by
  have e : ∀ (R : Type) [CommRing R], spMap (RingEquiv.refl R).toRingHom = 𝟙 _ := fun R _ =>
    Spec.map_id (CommRingCat.of R)
  obtain ⟨ρ, mu, h1, h2, h3, -⟩ := h σ (RingEquiv.refl _) (RingEquiv.refl _) r ν hw (fun _ _ => rfl) (fun _ => rfl)
    (by rw [e, Category.comp_id, hr])
  exact ⟨⟨s, σ, hs, hw, r, hr, ν, ρ, mu, by rw [h1, e, Category.comp_id], h2, h3⟩, rfl⟩

namespace Tw

variable {Z : Model Xo c β} (T : Tw Z)

def g : gen Z ≅ gen Z where
  hom := pullback.lift (genι Z ≫ T.ρ.hom) (genStr Z) (by rw [Category.assoc, T.specializationMap_comp_universalSection, pullback.condition])
  inv := pullback.lift (genι Z ≫ T.ρ.inv) (genStr Z) (by
    rw [Category.assoc, (Iso.inv_comp_eq _).2 T.specializationMap_comp_universalSection.symm, pullback.condition])
  hom_inv_id := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Iso.hom_inv_id]; simp)
    (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp])
  inv_hom_id := pullback.hom_ext
    (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Iso.inv_hom_id]; simp)
    (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp])

theorem g_ι : T.g.hom ≫ genι Z = genι Z ≫ T.ρ.hom := pullback.lift_fst _ _ _

theorem g_str : T.g.hom ≫ genStr Z = genStr Z := pullback.lift_snd _ _ _

theorem jQ_g : Z.jQ ≫ T.g.hom = T.r.hom ≫ Z.jQ :=
  pullback.hom_ext (by rw [Category.assoc, Category.assoc, T.g_ι, ← Category.assoc]; exact T.j_ρ)
    (by rw [Category.assoc, Category.assoc, T.g_str, Z.jQ_over, T.r_snd])

theorem mem_genBd (x : gen Z) : T.g.hom x ∈ genBd Z ↔ x ∈ genBd Z := by
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩
    refine ⟨T.r.inv z, ?_⟩
    have h1 : T.r.inv ≫ Z.jQ = Z.jQ ≫ T.g.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← T.jQ_g, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  · rintro ⟨z, rfl⟩
    exact ⟨T.r.hom z, by rw [← Scheme.Hom.comp_apply, ← T.jQ_g, Scheme.Hom.comp_apply]⟩

def sab : SABMap Z.t (GlobalTheory.FiniteStable.twist T.σ T.w0 Z.t) T.ρ.hom :=
  ⟨T.mu.cm, T.mu.cart, T.mu.base, T.mu.act, T.mu.lin⟩

theorem s_rt : T.s (H.rt : E) = H.rt := by
  have h := congrArg T.σ H.two_weight_eq_one_add_root
  rw [map_mul, map_ofNat, T.w0, H.two_weight_eq_one_add_root, map_add, map_one] at h
  rw [← T.coe_σ, ← add_left_cancel h]

abbrev emb (τ : E →+* ℂ) : E →+* ℂ := τ.comp (T.s : E →+* E)

def embEquiv : (E →+* ℂ) ≃ (E →+* ℂ) where
  toFun := T.emb
  invFun τ := τ.comp (T.s.symm : E →+* E)
  left_inv τ := RingHom.ext fun a => by simp
  right_inv τ := RingHom.ext fun a => by simp

theorem emb_rt (τ : E →+* ℂ) : T.emb τ (H.rt : E) = τ (H.rt : E) := congrArg τ T.s_rt

theorem mult_emb (τ : E →+* ℂ) : Dw.mult τ = Dw.mult (T.emb τ) := by
  unfold Datum.mult
  rw [T.emb_rt]

abbrev ix {τ : E →+* ℂ} (i : Fin (Dw.mult τ)) : Fin (Dw.mult (T.emb τ)) := Fin.cast (T.mult_emb τ) i

theorem embK_emb (τ : E →+* ℂ) (a : 𝓞 E) : embK c (T.emb τ) a = embK c τ (T.σ a) :=
  Subtype.ext (congrArg τ (T.coe_σ a).symm)

def letter : Letter Dw ≃ Letter Dw :=
  Equiv.sigmaCongr T.embEquiv fun τ => finCongr (T.mult_emb τ)

theorem letter_mk (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : T.letter ⟨τ, i⟩ = ⟨T.emb τ, T.ix i⟩ := rfl

def sym (a : Sym E) : Sym E := (a.1, a.2.1, Sum.map (fun p => (T.emb p.1, p.2)) id a.2.2)

section Frames

variable {R : Type} [CommRing R] {φ φ' : c.F →+* R} {x x' : Sp R ⟶ Z.X}

def Push (f : EigFrame Z φ x) (f' : EigFrame Z φ' x') : Prop :=
  φ' = φ ∧ x' = x ≫ T.ρ.hom ∧ ∀ τ i, f'.v τ i = f.v (T.emb τ) (T.ix i) ≫ T.mu.cm.F

def lie (hx : x ≫ T.ρ.hom = x') : TanM x Z.t.G ≃ₗ[R] TanM x' Z.t.G := pushE T.sab x hx

theorem left_lie (hx : x ≫ T.ρ.hom = x') (v : TanM x Z.t.G) : (tv (T.lie hx v)).left = (tv v).left ≫ T.mu.cm.F := rfl

theorem lie_act (hx : x ≫ T.ρ.hom = x') (a : 𝓞 E) (v : TanM x Z.t.G) :
    T.lie hx (actR Z.t.act a v) = actR Z.t.act (T.σ a) (T.lie hx v) := pushE_act T.sab x hx a v

theorem eig_iff (hx : x ≫ T.ρ.hom = x') (τ : E →+* ℂ) (v : TanM x Z.t.G) :
    (∀ a, actR Z.t.act a v = φ (embK c (T.emb τ) a) • v) ↔
      ∀ a, actR Z.t.act a (T.lie hx v) = φ (embK c τ a) • T.lie hx v := by
  refine ⟨fun h a => ?_, fun h a => (T.lie hx).injective ?_⟩
  · obtain ⟨a, rfl⟩ := T.σ.surjective a
    rw [← T.lie_act, h, map_smul, T.embK_emb]
  · rw [T.lie_act, h, map_smul, T.embK_emb]

theorem Push.vec {T : Tw Z} {f : EigFrame Z φ x} {f' : EigFrame Z φ' x'} (h : T.Push f f') (τ : E →+* ℂ)
    (i : Fin (Dw.mult τ)) : f'.vec τ i = T.lie h.2.1.symm (f.vec (T.emb τ) (T.ix i)) := tan_ext (h.2.2 τ i)

theorem exists_push (f : EigFrame Z φ x) (hφ : φ' = φ) (hx : x' = x ≫ T.ρ.hom) :
    ∃ f' : EigFrame Z φ' x', T.Push f f' := by
  subst hφ
  refine ⟨EigFrame.ofVec (fun τ i => T.lie hx.symm (f.vec (T.emb τ) (T.ix i)))
    (fun τ i => (T.eig_iff hx.symm τ _).1 (f.act_vec _ _)) fun τ w hw => ?_, rfl, hx, fun _ _ => rfl⟩
  obtain ⟨w, rfl⟩ := (T.lie hx.symm).surjective w
  have h := f.existsUnique_sum (T.emb τ) w ((T.eig_iff hx.symm τ _).2 hw)
  refine (Equiv.existsUnique_congr (Equiv.arrowCongr (finCongr (T.mult_emb τ)) (Equiv.refl R)) fun a => ?_).2 h
  rw [← (T.lie hx.symm).injective.eq_iff, map_sum, ← (finCongr (T.mult_emb τ)).sum_comp]
  simp

theorem exists_pull (f' : EigFrame Z φ' x') (hφ : φ' = φ) (hx : x' = x ≫ T.ρ.hom) :
    ∃ f : EigFrame Z φ x, T.Push f f' := by
  subst hφ
  have key : ∀ z : Letter Dw, ∃ v : TanM x Z.t.G,
      T.lie hx.symm v = f'.vec (T.letter.symm z).1 (T.letter.symm z).2 := fun z => (T.lie hx.symm).surjective _
  choose u hu using key
  have hu' : ∀ τ i, T.lie hx.symm (u ⟨T.emb τ, T.ix i⟩) = f'.vec τ i := fun τ i => by
    rw [hu, ← T.letter_mk, Equiv.symm_apply_apply]
  refine ⟨EigFrame.ofVec (fun τ i => u ⟨τ, i⟩) (fun τ i => ?_) fun τ w hw => ?_, rfl, hx,
    fun τ i => (congrArg (fun v => (tv v).left) (hu' τ i)).symm⟩
  · obtain ⟨τ, rfl⟩ := T.embEquiv.surjective τ
    obtain ⟨i, rfl⟩ := (finCongr (T.mult_emb τ)).surjective i
    refine (T.eig_iff hx.symm τ _).2 fun a => ?_
    erw [hu']
    exact f'.act_vec τ i a
  · obtain ⟨τ, rfl⟩ := T.embEquiv.surjective τ
    have h := f'.existsUnique_sum τ _ ((T.eig_iff hx.symm τ _).1 hw)
    refine (Equiv.existsUnique_congr (Equiv.arrowCongr (finCongr (T.mult_emb τ)) (Equiv.refl R)) fun a => ?_).1 h
    rw [← (T.lie hx.symm).injective.eq_iff (a := w), map_sum]
    refine iff_of_eq (congrArg _ (Fintype.sum_equiv (finCongr (T.mult_emb τ)) _ _ fun i => ?_))
    rw [map_smul, ← hu']
    simp
    rfl

theorem Push.co {T : Tw Z} {f g : EigFrame Z φ x} {f' g' : EigFrame Z φ' x'} (hf : T.Push f f') (hg : T.Push g g')
    (τ : E →+* ℂ) : f'.co g' τ = (f.co g (T.emb τ)).submatrix T.ix T.ix :=
  EigFrame.co_eq fun i => (isComb_iff (f'.vec τ) _ (g'.vec τ i)).2 (by
    rw [hg.vec, f.vec_eq g, map_sum, ← (finCongr (T.mult_emb τ)).sum_comp]
    simp only [map_smul, hf.vec]
    rfl)

theorem Push.map {T : Tw Z} {f : EigFrame Z φ x} {f' : EigFrame Z φ' x'} (h : T.Push f f') {R' : Type} [CommRing R']
    {ψ : R →+* R'} {χ χ' : c.F →+* R'} {y y' : Sp R' ⟶ Z.X} {g : EigFrame Z χ y} {g' : EigFrame Z χ' y'}
    (hg : f.IsMap ψ g) (hg' : f'.IsMap ψ g') (hχ : χ' = χ) (hy : y' = y ≫ T.ρ.hom) : T.Push g g' :=
  ⟨hχ, hy, fun τ i => by rw [hg', hg, h.2.2, Category.assoc]⟩

theorem Push.tri_iff {T : Tw Z} {f : EigFrame Z φ x} {f' : EigFrame Z φ' x'} (h : T.Push f f') {R' : Type} [CommRing R']
    {ψ : R →+* R'} {χ χ' : c.F →+* R'} {y y' : Sp R' ⟶ Z.X} {g : EigFrame Z χ y} {g' : EigFrame Z χ' y'}
    (hg : T.Push g g') {t t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ} (ht : ∀ τ i, t (T.emb τ) (T.ix i) = t' τ i) :
    f.Tri ψ g t ↔ f'.Tri ψ g' t' := by
  have hx : y = spMap ψ ≫ x ↔ y' = spMap ψ ≫ x' := by
    rw [hg.2.1, h.2.1, ← Category.assoc, cancel_mono]
  have hφ : χ = ψ.comp φ ↔ χ' = ψ.comp φ' := by rw [hg.1, h.1]
  have key (h1 : y = spMap ψ ≫ x) (h2 : χ = ψ.comp φ) : ∃ (k : EigFrame Z χ y) (k' : EigFrame Z χ' y'),
      f.IsMap ψ k ∧ f'.IsMap ψ k' ∧ ∀ τ, k'.co g' τ = (k.co g (T.emb τ)).submatrix T.ix T.ix := by
    obtain ⟨k, hk⟩ := f.exists_isMap ψ h2 h1
    obtain ⟨k', hk'⟩ := f'.exists_isMap ψ (hφ.1 h2) (hx.1 h1)
    exact ⟨k, k', hk, hk', (h.map hk hk' hg.1 hg.2.1).co hg⟩
  constructor
  · intro a
    obtain ⟨k, k', hk, hk', e⟩ := key a.1 a.2.1
    refine ⟨hx.1 a.1, hφ.1 a.2.1, fun τ i => ⟨fun j => k'.co g' τ j i, ?_, fun j hj => ?_, ?_⟩⟩
    · rw [e, ← ht]; exact (a.co _ hk).2 _
    · rw [e]; exact (a.co _ hk).1 _ _ hj
    · rw [← funext (hk' τ)]; exact k'.co_spec g' τ i
  · intro a
    obtain ⟨k, k', hk, hk', e⟩ := key (hx.2 a.1) (hφ.2 a.2.1)
    refine ⟨hx.2 a.1, hφ.2 a.2.1, fun τ i => ⟨fun j => k.co g τ j i, ?_, fun j hj => ?_, ?_⟩⟩
    · obtain ⟨τ, rfl⟩ := T.embEquiv.surjective τ
      obtain ⟨i, rfl⟩ := (finCongr (T.mult_emb τ)).surjective i
      exact ((congrFun (congrFun (e τ) i) i).symm.trans ((a.co _ hk').2 i)).trans (congrArg _ (ht τ i).symm)
    · obtain ⟨τ, rfl⟩ := T.embEquiv.surjective τ
      obtain ⟨i, rfl⟩ := (finCongr (T.mult_emb τ)).surjective i
      obtain ⟨j, rfl⟩ := (finCongr (T.mult_emb τ)).surjective j
      exact (congrFun (congrFun (e τ) j) i).symm.trans ((a.co _ hk').1 _ _ hj)
    · rw [← funext (hk τ)]; exact k.co_spec g τ i

theorem exists_relab {G : Type} (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G) :
    ∃ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G, ∀ τ i, t (T.emb τ) (T.ix i) = t' τ i :=
  ⟨fun τ i => t' (T.letter.symm ⟨τ, i⟩).1 (T.letter.symm ⟨τ, i⟩).2, fun τ i => by
    beta_reduce
    rw [← T.letter_mk, Equiv.symm_apply_apply]⟩

end Frames

theorem letterOf_emb (τ : E →+* ℂ) (k : ℕ) :
    letterOf Dw (.inl (T.emb τ, k)) = (letterOf Dw (.inl (τ, k))).map T.letter := by
  by_cases h : k < Dw.mult τ
  · rw [letterOf, letterOf, dif_pos h, dif_pos (T.mult_emb τ ▸ h)]; rfl
  · rw [letterOf, letterOf, dif_neg h, dif_neg (T.mult_emb τ ▸ h)]; rfl

theorem expo_sym {w : Sym E →₀ ℤ} (hw : ∀ a ∈ w.support, a.2.2.isLeft = true) (z : Letter Dw) :
    expo Dw (w.mapDomain T.sym) (T.letter z) = expo Dw w z := by
  classical
  rw [expo, expo, Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => by split_ifs <;> simp)]
  refine Finsupp.sum_congr fun a ha => ?_
  obtain ⟨b, R, ⟨τ, k⟩ | k⟩ := a
  · refine if_congr ?_ rfl rfl
    change letterOf Dw (.inl (T.emb τ, k)) = _ ↔ _
    rw [T.letterOf_emb]
    exact (Option.map_injective T.letter.injective).eq_iff (b := some z)
  · exact absurd (hw _ ha) (by simp)

def LnPush : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (b : Bool) (x : Sp ℂ_[p] ⟶ Z.X)
    (u u' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left)), (∀ τ i, IsTanAtG Z.t x (u τ i)) →
    (∀ τ i, u' τ i = u (T.emb τ) (T.ix i) ≫ T.mu.cm.F) → ∀ (τ : E →+* ℂ) (k : ℕ),
      lnStep Z.t x u p b (.inl (T.emb τ, k)) = lnStep Z.t (x ≫ T.ρ.hom) u' p b (.inl (τ, k))

variable {σ : c.F →+* ℂ}

def pt (y : CxPts (genStr Z) σ) : CxPts (genStr Z) σ := ⟨y.1 ≫ T.g.hom, by rw [Category.assoc, T.g_str, y.2]⟩

theorem pt_ι (y : CxPts (genStr Z) σ) : (T.pt y).1 ≫ genι Z = (y.1 ≫ genι Z) ≫ T.ρ.hom := by
  rw [pt, Category.assoc, T.g_ι, Category.assoc]

def MetAt (y : CxPts (genStr Z) σ) (G G' : EigMet Z σ) : Prop :=
  ∀ (f : EigFrame Z σ (y.1 ≫ genι Z)) (f' : EigFrame Z σ ((T.pt y).1 ≫ genι Z)), T.Push f f' → ∀ τ,
    G.gram (T.pt y) f' τ = (G'.gram y f (T.emb τ)).submatrix T.ix T.ix

variable {F : Type} [Field F] {e : F ≃+* c.F} (C C' : FlagCpt Z e)

def PtRel {K : Type} [Field K] (p : Sp K ⟶ C.Y.X) (p' : Sp K ⟶ C'.Y.X) : Prop :=
  p' ≫ C'.π = p ≫ C.π ≫ T.g.hom ∧ ∃ (χ : c.F →+* K) (f : EigFrame Z χ (p ≫ C.π ≫ genι Z))
    (f' : EigFrame Z χ (p' ≫ C'.π ≫ genι Z)), p ≫ C.π ≫ genStr Z = spMap χ ∧ T.Push f f' ∧ C.Carries p f ∧ C'.Carries p' f'

variable (φ : C.Y.X ≅ C'.Y.X) (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)

def GenRel : Prop :=
  φ.hom ≫ C'.π = C.π ≫ T.g.hom ∧ genericPt C.Y ≫ φ.hom = spMap ψ ≫ genericPt C'.Y ∧
    ∃ g₀ : EigFrame Z (constF e C.Y) ((genericPt C.Y ≫ C.π ≫ genι Z) ≫ T.ρ.hom), T.Push C.f0 g₀ ∧ C'.f0.Tri ψ g₀ t₀

def LocRel : Prop :=
  φ.hom ≫ C'.π = C.π ≫ T.g.hom ∧ genericPt C.Y ≫ φ.hom = spMap ψ ≫ genericPt C'.Y ∧
    ∀ (y : C.Y.X) (y' : C'.Y.X) (χ' : c.F →+* C'.Y.X.presheaf.stalk y')
      (f' : EigFrame Z χ' (stalkPt C'.Y y' ≫ C'.π ≫ genι Z)) (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C'.Y.Fnˣ),
      y' = φ.hom y → f'.Tri (algebraMap (C'.Y.X.presheaf.stalk y') C'.Y.X.functionField) C'.f0 t' →
      ∃ (a : C'.Y.X.presheaf.stalk y' →+* C.Y.X.presheaf.stalk y) (χ : c.F →+* C.Y.X.presheaf.stalk y)
        (f : EigFrame Z χ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
        stalkPt C.Y y ≫ φ.hom = spMap a ≫ stalkPt C'.Y y' ∧ χ = a.comp χ' ∧
        (∀ z, ψ (algebraMap (C'.Y.X.presheaf.stalk y') C'.Y.X.functionField z) =
          algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField (a z)) ∧
        f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t ∧
        (∀ τ i, t (T.emb τ) (T.ix i) = Units.map (ψ : C'.Y.Fn →* C.Y.Fn) (t' τ i) * t₀ τ i) ∧
        ∀ τ i, spMap (dualMap a) ≫ f'.v τ i = f.v (T.emb τ) (T.ix i) ≫ T.mu.cm.F

end Tw

section large₂

variable {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def lgFr (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) [Fact (resP v).Prime]
    {χ : c.F →+* Y.Y.X.presheaf.stalk (below y.1)} (f : EigFrame Z χ (stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z))
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) : ℝ :=
  let ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
  Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
      (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
    (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
        (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2

def LgIndep : Prop :=
  ∀ (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) [Fact (resP v).Prime]
    (χ : c.F →+* Y.Y.X.presheaf.stalk (below y.1)) (f : EigFrame Z χ (stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z))
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ), (∀ a ∈ w.support, a.2.2.isLeft = true) →
    f.Tri (algebraMap (Y.Y.X.presheaf.stalk (below y.1)) Y.Y.X.functionField) Y.f0 t → lgOf Y w v ε y = lgFr Y w v ε y f t

omit [NumberField F] in

def TriEqn : Prop :=
  ∀ (y : Y.Y.X) (χ : c.F →+* Y.Y.X.presheaf.stalk y) (f : EigFrame Z χ (stalkPt Y.Y y ≫ Y.π ≫ genι Z))
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ),
    f.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t → ∀ τ i, (Y.gr τ i).IsEqn y (t τ i)

end large₂

end GlobalTheory.ShFam.GalCarry
