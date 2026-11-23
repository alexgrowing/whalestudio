import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)

section Relations

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' S'' : Finset ℕ}
  {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω''] {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : K → Type} {J' : K' → Type} {J'' : K'' → Type} {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'}
  {x'' : (Σ k, J'' k) → Ω''}

def HodgeOver (A' : HodgeCpt Y S' x') (A : HodgeCpt Y S x) (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) :
    Prop :=
  GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ h i ∧ A'.f = h ≫ A.f ∧ A'.cst = i.comp A.cst ∧ IsExtOver i j ∧
    ∀ w, (A'.M.pt (j w)).left ≫ A'.m.φ = spMap (dualMap i) ≫ (A.M.pt w).left ≫ A.m.φ

abbrev WBases (A : HodgeCpt Y S x) : Type := ∀ τ : CMType H, Module.Basis (Fin D.p) Ω (A.Vgen (.inl τ))

abbrev OmBases (A : HodgeCpt Y S x) : Type :=
  ∀ τ : CMType H, Module.Basis (Fin D.q) Ω (Module.Dual Ω (A.Vgen (.inr τ)))

def BasesOver {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} (i : Ω →+* Ω') (j : A.Li →+ A'.Li)
    (bW' : WBases A') (bO' : OmBases A') (bW : WBases A) (bO : OmBases A) : Prop :=
  (∀ τ a, (bW' τ a : A'.Li) = j (bW τ a)) ∧
    ∀ τ a (v : A.Vgen (.inr τ)) (v' : A'.Vgen (.inr τ)), (v' : A'.Li) = j v → bO' τ a v' = i (bO τ a v)

def HasSncBoundary [CharZero Ω] [∀ k, Fintype (J k)] (A : HodgeCpt Y S x) (n : ℕ) : Prop :=
  ∃ bd : Ideal (MRing J), Cmp.IsSncModel x n bd ∧
    ∀ (z : Spec (CommRingCat.of ℂ) ⟶ A.X) w, CoordsAt A.ξ x z w → (w ∈ mcPts bd ↔ ¬ A.Interior z)

variable {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

def FlagTie.IsTotal (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y) (Fl : 𝔐'.Flag)
    (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Φ) : Prop :=
  (∃ (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li), HodgeOver 𝔐' 𝔐 pr (algebraMap M.Ω Φ) j ∧ 𝔐'.R = 𝔐.R ∧
    (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) ∧
    (∀ τ (k : Fin D.p), Fl.b (.inl τ) k = colFrame (fun a => j (tie.eW τ a)) (wBlock (M.g τ)) k) ∧
    ∀ τ (v : Fin D.q → 𝔐.Vgen (.inr τ)), (∀ a b, tie.eO τ a (v b) = if a = b then 1 else 0) →
      ∀ k : Fin D.q, Fl.b (.inr τ) k = colFrame (fun a => j (v a)) (omBlock (M.g τ))ᵀ⁻¹ k.rev) ∧
  Fl.RootLines xdeg e ∧ (∀ τ i, M.dy (τ, i) = -∑ k ∈ Finset.Iic i, xdeg (τ, k)) ∧
  ∀ τ i, (∏ k ∈ Finset.Iic i, e (τ, k)) * detFac D.p i (M.g τ) *
    (M.blk (τ, i)).elim (algebraMap M.Ω Φ (M.lam (τ, i))) (fun _ => 1) = 1

end Relations

def BaseMetric.IsConj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) : Prop :=
  (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) →
    (x' ∈ ReciprocityTheory.AnForm.P.bdry BM.s ↔ x ∈ ReciprocityTheory.AnForm.P.bdry BM.s) ∧
      ReciprocityTheory.AnForm.P.rW BM.L BM.s x' = ReciprocityTheory.AnForm.P.rW BM.L BM.s x) ∧
  ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ ReciprocityTheory.AnForm.P.bdry BM.s →
    SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z

def FlagModelExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀)
    (n d : ℕ) (bW : WBases 𝔐) (bO : OmBases 𝔐), IsArithVar (mCoordIdeal x₀) (n + 1) → 𝔐.IsCover d →
    ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (Φ : Type) (_ : Field Φ)
      (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐₁ : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐₁)
      (κ : K₀ → NonPluckerBlocks M.blk) (v : (Σ k, J₀ k) → Σ k, baseIdx ι M.blk k) (φ : Ω →+* M.Ω) (π : 𝔐₁.X ⟶ 𝔐.X)
      (j : 𝔐.Li →+ 𝔐₁.Li) (𝔐' : HodgeCpt Y S y) (Fl : 𝔐'.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
      (e : CMType H × Fin (D.p + D.q) → Φ),
      (IsBlockMap κ v ∧ (∀ q, M.x (v q) = φ (x₀ q)) ∧ Function.Bijective φ ∧ IsIso π ∧ HodgeOver 𝔐₁ 𝔐 π φ j ∧
        𝔐₁.R = 𝔐.R ∧ BasesOver φ j tie.eW tie.eO bW bO) ∧
      (𝔐₁.IsCover d ∧ IsArithVar (mCoordIdeal M.x) (n + 1) ∧ ∀ m, HasSncBoundary 𝔐 m → HasSncBoundary 𝔐₁ m) ∧
      IsArithVar (mCoordIdeal y) (n + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) ∧
      tie.IsTotal 𝔐' Fl xdeg e ∧ Fl.deg = d

def CoverExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S' : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ')
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (M' : FlagModel y' (CMType H) (D.p + D.q) D.p)
    (𝔐 : HodgeCpt Y S M.x) (𝔐' : HodgeCpt Y S' M'.x) (tie : FlagTie M 𝔐) (tie' : FlagTie M' 𝔐')
    (κ : NonPluckerBlocks M.blk → NonPluckerBlocks M'.blk) (v : (Σ k, baseIdx ι M.blk k) → Σ k, baseIdx ι' M'.blk k)
    (φ : M.Ω →+* M'.Ω) (h : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (d d' : ℕ),
    IsBlockMap κ v → (∀ q, M'.x (v q) = φ (M.x q)) → HodgeOver 𝔐' 𝔐 h φ j →
    BasesOver φ j tie'.eW tie'.eO tie.eW tie.eO → 𝔐.IsCover d → 𝔐'.IsCover d' →
    ∃ Cv : FlagCover M' M, Cv.κ = κ ∧ Cv.v = v ∧ Cv.φ = φ ∧ d * Cv.deg = d'

def BaseMetricExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐) (d : ℕ),
    1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover d → HasSncBoundary 𝔐 (Fintype.card (CMType H) * D.p * D.q) →
    ∃ BM : BaseMetric M (Fintype.card (CMType H) * D.p * D.q), BM.IsHodge tie ∧ BM.IsConj

def TieSt : Prop := FlagModelExists ∧ CoverExists ∧ BaseMetricExists

section Tests

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' S'' : Finset ℕ}
  {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω''] {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : K → Type} {J' : K' → Type} {J'' : K'' → Type} {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'}
  {x'' : (Σ k, J'' k) → Ω''}

theorem card_mul_eq_dim (D : Datum H) : Fintype.card (CMType H) * D.p * D.q = D.dim := by
  rw [Fintype.card_eq_nat_card, Datum.dim]
  exact congrArg (· * D.p * D.q) (GlobalTheory.PeriodCoord.card_cmType H)

theorem HodgeOver.refl (A : HodgeCpt Y S x) : HodgeOver A A (𝟙 _) (RingHom.id Ω) (AddMonoidHom.id _) := by
  have e : dualMap (RingHom.id Ω) = RingHom.id _ := RingHom.ext fun a => TrivSqZeroExt.inl_fst_add_inr_snd_eq a
  refine ⟨?_, (Category.id_comp _).symm, rfl, ⟨fun _ _ => rfl, fun _ _ h => h⟩, fun w => ?_⟩
  · show A.ξ ≫ 𝟙 _ = Spec.map (𝟙 _) ≫ A.ξ
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  · rw [e]
    show _ = Spec.map (𝟙 _) ≫ _
    rw [Spec.map_id, Category.id_comp]
    rfl

theorem HodgeOver.trans {A'' : HodgeCpt Y S'' x''} {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h' : A''.X ⟶ A'.X}
    {h : A'.X ⟶ A.X} {i' : Ω' →+* Ω''} {i : Ω →+* Ω'} {j' : A'.Li →+ A''.Li} {j : A.Li →+ A'.Li}
    (a : HodgeOver A'' A' h' i' j') (b : HodgeOver A' A h i j) :
    HodgeOver A'' A (h' ≫ h) (i'.comp i) (j'.comp j) := by
  have e : dualMap (i'.comp i) = (dualMap i').comp (dualMap i) := RingHom.ext fun a => by
    ext <;> simp [dualMap]
  refine ⟨?_, by rw [a.2.1, b.2.1, Category.assoc], by rw [a.2.2.1, b.2.2.1, RingHom.comp_assoc],
    ⟨fun t w => ?_, fun n v hv => a.2.2.2.1.2 n _ (b.2.2.2.1.2 n v hv)⟩, fun w => ?_⟩
  · show _ = Spec.map (CommRingCat.ofHom i ≫ CommRingCat.ofHom i') ≫ _
    rw [← Category.assoc, a.1, Category.assoc, b.1, Spec.map_comp, Category.assoc]
  · show j' (j (t • w)) = i' (i t) • j' (j w)
    rw [b.2.2.2.1.1, a.2.2.2.1.1]
  · show (A''.M.pt (j' (j w))).left ≫ _ = _
    rw [a.2.2.2.2, b.2.2.2.2, e]
    show _ = Spec.map (CommRingCat.ofHom (dualMap i) ≫ CommRingCat.ofHom (dualMap i')) ≫ _
    rw [Spec.map_comp, Category.assoc]

variable {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h : A'.X ⟶ A.X} {i : Ω →+* Ω'} {j : A.Li →+ A'.Li}

theorem HodgeOver.map_act (a : HodgeOver A' A h i j) (t : 𝓞 E) (w : A.Li) : j (A.ρ t w) = A'.ρ t (j w) := by
  refine A'.M.inj (Over.OverMorphism.ext (A'.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  have h1 := a.2.2.2.2 (A.ρ t w)
  rw [A.act t w, Over.comp_left, Category.assoc, A.m.act] at h1
  refine h1.trans ?_
  rw [A'.act t (j w), Over.comp_left, Category.assoc, A'.m.act, ← Category.assoc (A'.M.pt (j w)).left]
  have h2 := a.2.2.2.2 w
  simp only [SABMap.φ] at h2
  rw [h2, Category.assoc, Category.assoc]

theorem HodgeOver.map_Vgen (a : HodgeOver A' A h i j) (s : CMType H ⊕ CMType H) {w : A.Li} (hw : w ∈ A.Vgen s) :
    j w ∈ A'.Vgen s := by
  refine (Submodule.mem_iInf _).2 fun t => ?_
  have h1 : A.ρ t w - A.emb s t • w = 0 := (Submodule.mem_iInf _).1 hw t
  show A'.ρ t (j w) - A'.emb s t • j w = 0
  have e : A'.emb s t = i (A.emb s t) := by
    show A'.cst _ = i (A.cst _)
    rw [a.2.2.1]; rfl
  rw [← a.map_act, e, ← a.2.2.2.1.1, ← map_sub, h1, map_zero]

theorem nonempty_basis_Vgen (A : HodgeCpt Y S x) (s : CMType H ⊕ CMType H) :
    Nonempty (Module.Basis (Fin (labelRk D s)) Ω (A.Vgen s)) := by
  obtain ⟨U, hU, b, hb, hf⟩ := (Lat.restrict_isVBOn _ _ _ _ _ _ _ _ (A.vb s)).1 (CptModel.self A.ξ) trivial
  exact ⟨Module.Basis.mk (hf _ trivial hU).1 hb.ge⟩

theorem nonempty_bases (A : HodgeCpt Y S x) : Nonempty (WBases A) ∧ Nonempty (OmBases A) :=
  ⟨⟨fun τ => (nonempty_basis_Vgen A (.inl τ)).some⟩, ⟨fun τ => (nonempty_basis_Vgen A (.inr τ)).some.dualBasis⟩⟩

theorem HodgeOver.exists_basis (a : HodgeOver A' A h i j) (s : CMType H ⊕ CMType H)
    (b : Module.Basis (Fin (labelRk D s)) Ω (A.Vgen s)) :
    ∃ b' : Module.Basis (Fin (labelRk D s)) Ω' (A'.Vgen s), ∀ k, (b' k : A'.Li) = j (b k) := by
  obtain ⟨B⟩ := nonempty_basis_Vgen A' s
  have := Module.Finite.of_basis B
  have h1 := a.2.2.2.1.2 _ _ (b.linearIndependent.map' (A.Vgen s).subtype (Submodule.ker_subtype _))
  let w : Fin (labelRk D s) → A'.Vgen s := fun k => ⟨j (b k), a.map_Vgen s (b k).2⟩
  have h2 : LinearIndependent Ω' w := LinearIndependent.of_comp (A'.Vgen s).subtype h1
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' w h2 (Module.finrank_eq_card_basis B).symm, fun k => by simp [w]⟩

theorem HodgeOver.exists_basesOver (a : HodgeOver A' A h i j) (bW : WBases A) (bO : OmBases A) :
    ∃ (bW' : WBases A') (bO' : OmBases A'), BasesOver i j bW' bO' bW bO := by
  choose bW' hW using fun τ => a.exists_basis (.inl τ) (bW τ)
  have key : ∀ τ, ∃ b' : Module.Basis (Fin D.q) Ω' (Module.Dual Ω' (A'.Vgen (.inr τ))),
      ∀ k (v : A.Vgen (.inr τ)) (v' : A'.Vgen (.inr τ)), (v' : A'.Li) = j v → b' k v' = i (bO τ k v) := fun τ => by
    obtain ⟨B⟩ := nonempty_basis_Vgen A (.inr τ)
    have := Module.Finite.of_basis B
    let C : Module.Basis (Fin D.q) Ω (A.Vgen (.inr τ)) := (bO τ).dualBasis.map (Module.evalEquiv Ω _).symm
    have hC : ∀ v k, C.repr v k = bO τ k v := fun v k => by
      simp [C]
    obtain ⟨C', hC'⟩ : ∃ C' : Module.Basis (Fin D.q) Ω' (A'.Vgen (.inr τ)), ∀ k, (C' k : A'.Li) = j (C k) :=
      a.exists_basis (.inr τ) C
    refine ⟨C'.dualBasis, fun k v v' hv => ?_⟩
    have e : v' = ∑ m, i (bO τ m v) • C' m := Subtype.ext (by
      rw [hv]
      conv_lhs => rw [← C.sum_repr v]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, map_sum, a.2.2.2.1.1, hC', hC])
    rw [e, Module.Basis.dualBasis_apply, C'.repr_sum_self]
  choose bO' hO using key
  exact ⟨bW', bO', hW, hO⟩

theorem BasesOver.refl (bW : WBases A) (bO : OmBases A) :
    BasesOver (RingHom.id Ω) (AddMonoidHom.id _) bW bO bW bO :=
  ⟨fun _ _ => rfl, fun τ a v v' e => by rw [show v' = v from Subtype.ext e]; rfl⟩

theorem colFrame_dual {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ} (φ : Fin r → Module.Dual Ω V) (v : Fin r → V)
    (hv : ∀ a b, φ a (v b) = if a = b then 1 else 0) (g : Matrix (Fin r) (Fin r) Ω) (hg : IsUnit g.det) (k m : Fin r) :
    colFrame φ g k (colFrame v gᵀ⁻¹ m) = if k = m then 1 else 0 := by
  have := congrFun (congrFun (Matrix.mul_nonsing_inv gᵀ (by rwa [det_transpose])) k) m
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  rw [← this]
  simp [colFrame, hv, mul_comm]

example (τ : CMType H) (a : Fin D.q) :
    HodgeCpt.rootIdx D (τ, ⟨D.p + a, by omega⟩) = ⟨.inr τ, a.rev⟩ := by
  have : ¬ D.p + (a : ℕ) < D.p := by omega
  simp only [HodgeCpt.rootIdx, this, dif_neg, not_false_eq_true]
  congr 1
  exact Fin.ext (by simp [Fin.rev]; omega)

variable {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}

theorem FlagTie.IsTotal.central {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}
    {tie : FlagTie M 𝔐} {𝔐' : HodgeCpt Y S y} {Fl : 𝔐'.Flag} {xdeg : CMType H × Fin (D.p + D.q) → K → ℤ}
    {e : CMType H × Fin (D.p + D.q) → Φ} (ht : tie.IsTotal 𝔐' Fl xdeg e)
    {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F) (τ : CMType H) (k : Fin (D.p + D.q))
    (hk : M.blk (τ, k) = none) :
    algebraMap M.Ω Φ (detFac D.p k (F.T τ)) = algebraMap M.Ω Φ ((∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, k) k') * F.υ (τ, k)) *
      (∏ m ∈ Finset.Iic k, e (τ, m)) * detFac D.p k (M.g τ) := by
  have h1 := ht.2.2.2 τ k
  rw [hk, Option.elim_none] at h1
  rw [← hF.2.2.2 (τ, k) hk, map_mul]
  linear_combination (-algebraMap M.Ω Φ (detFac D.p k (F.T τ))) * h1

example (xdeg : Unit × Fin 2 → Bool → ℤ)
    (h : ∀ i, (FlagEx.MH (![1, 1, 0] : Fin 3 → ℚ) rfl (Or.inl one_ne_zero)).dy ((), i) =
      -∑ k ∈ Finset.Iic i, xdeg ((), k)) :
    (xdeg ((), 0) false = 1 ∧ xdeg ((), 0) true = -1) ∧ xdeg ((), 1) false = 0 ∧ xdeg ((), 1) true = 1 := by
  have hb : ∀ p, FlagEx.blkH p ≠ some false := fun p h => by simpa using (FlagEx.blkH_some h).2
  have ht : ¬ ∀ p, FlagEx.blkH p ≠ some true := fun h => h ((), 0) rfl
  let M := FlagEx.MH (![1, 1, 0] : Fin 3 → ℚ) rfl (Or.inl one_ne_zero)
  have a₀ := (show M.dy ((), 0) false = -1 from dif_pos hb).symm.trans (congrFun (h 0) false)
  have a₁ := (show M.dy ((), 0) true = 1 from (dif_neg ht).trans (if_pos rfl)).symm.trans (congrFun (h 0) true)
  have b₀ := (show M.dy ((), 1) false = -1 from dif_pos hb).symm.trans (congrFun (h 1) false)
  have b₁ := (show M.dy ((), 1) true = 0 from (dif_neg ht).trans (if_neg (by decide))).symm.trans
    (congrFun (h 1) true)
  have e₀ : Finset.Iic (0 : Fin 2) = {0} := by decide
  have e₁ : Finset.Iic (1 : Fin 2) = {0, 1} := by decide
  simp only [e₀, e₁, Finset.sum_singleton, Pi.neg_apply, Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide),
    Pi.add_apply] at a₀ a₁ b₀ b₁
  omega

theorem conj_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    (fun q => starRingEnd ℂ (z q)) ∈ mcPts P := by
  refine ⟨fun k => (hz.1 k).imp fun i hi => (map_ne_zero _).2 hi, fun f hf => ?_⟩
  have h := congrArg (starRingEnd ℂ) (hz.2 f hf)
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left, map_zero] at h
  rw [MvPolynomial.eval_map, ← h]
  exact congrArg (fun g => MvPolynomial.eval₂ g _ f) (RingHom.ext_int _ _)

variable {Ψ : Type} {N j n : ℕ} {M : FlagModel y Ψ N j}

theorem BaseMetric.exists_conj (BM : BaseMetric M n) (x : BM.Rb.X) :
    ∃ x', SameOrbit (BM.Rb.lift x' x') fun q => starRingEnd ℂ (BM.Rb.lift x x q) :=
  BM.Rb.surj _ (conj_mem_mcPts (BM.Rb.mem x x (BM.Rb.mem_U x))) fun h => by simpa using h.2 1 trivial

theorem BaseMetric.isConj_of_isEmpty (BM : BaseMetric M n) [IsEmpty (NonPluckerBlocks M.blk)]
    (h : ∀ p, IsConjInvariantH (BM.hom p)) : BM.IsConj := by
  refine ⟨fun x x' _ => ?_, fun p z _ _ _ _ => h p z⟩
  obtain rfl : x' = x := BM.Rb.inj _ _ (fun h => by simpa using h.2 1 trivial)
    ⟨fun _ => 1, fun _ => one_ne_zero, funext fun q => isEmptyElim q.1⟩
  exact ⟨Iff.rfl, rfl⟩

end Tests

section Chain

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S S' : Finset ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω] {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {x₀ : (Σ k, J₀ k) → Ω}

theorem exists_flagModel_baseMetric (ha : FlagModelExists) (hc : BaseMetricExists) (𝔐 : HodgeCpt Y S x₀) {d : ℕ}
    (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) (hv : IsArithVar (mCoordIdeal x₀) (Fintype.card (CMType H) * D.p * D.q + 1))
    (hd : 𝔐.IsCover d) (hs : HasSncBoundary 𝔐 (Fintype.card (CMType H) * D.p * D.q)) :
    ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (Φ : Type) (_ : Field Φ)
      (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐₁ : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐₁)
      (BM : BaseMetric M (Fintype.card (CMType H) * D.p * D.q)), BM.IsHodge tie ∧ BM.IsConj ∧
      IsArithVar (mCoordIdeal y)
        (Fintype.card (CMType H) * D.p * D.q + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  obtain ⟨⟨bW⟩, ⟨bO⟩⟩ := nonempty_bases 𝔐
  obtain ⟨K, _, ι, _, Φ, _, y, M, 𝔐₁, tie, -, -, -, -, -, -, -, -, -, -, ⟨h1, -, h2⟩, h3, -⟩ :=
    ha E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 _ d bW bO hv hd
  obtain ⟨BM, hBM, hcj⟩ := hc E H D l Xo c Y S K ι Φ y M 𝔐₁ tie d hp hq h1 (h2 _ hs)
  exact ⟨K, _, ι, _, Φ, _, y, M, 𝔐₁, tie, BM, hBM, hcj, h3⟩

theorem exists_flagCover (ha : FlagModelExists) (hb : CoverExists) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {M : FlagModel y (CMType H) (D.p + D.q) D.p}
    {𝔐 : HodgeCpt Y S M.x} (tie : FlagTie M 𝔐) (A : HodgeCpt Y S' x₀) {κ : NonPluckerBlocks M.blk → K₀}
    {v : (Σ k, baseIdx ι M.blk k) → Σ k, J₀ k} {i : M.Ω →+* Ω} {h : A.X ⟶ 𝔐.X} {j : 𝔐.Li →+ A.Li} {n d d' : ℕ}
    (hκ : IsBlockMap κ v) (hx : ∀ q, x₀ (v q) = i (M.x q)) (ho : HodgeOver A 𝔐 h i j)
    (hv : IsArithVar (mCoordIdeal x₀) (n + 1)) (hd : 𝔐.IsCover d) (hd' : A.IsCover d') :
    ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (Φ' : Type) (_ : Field Φ')
      (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' (CMType H) (D.p + D.q) D.p) (Cv : FlagCover M' M)
      (𝔐' : HodgeCpt Y S' y') (Fl : 𝔐'.Flag), d * Cv.deg = Fl.deg := by
  obtain ⟨bW, bO, hB⟩ := ho.exists_basesOver tie.eW tie.eO
  obtain ⟨K', _, ι', _, Φ', _, y', M', 𝔐₁, tie', κ', v', φ, π, j', 𝔐', Fl, -, -, ⟨g1, g2, -, -, g3, -, g4⟩,
    ⟨h1, -, -⟩, -, -, h4⟩ := ha E H D l Xo c Y S' Ω K₀ J₀ x₀ A n d' bW bO hv hd'
  have hκ' : IsBlockMap (κ' ∘ κ) (v' ∘ v) := by
    refine ⟨g1.1.comp hκ.1, g1.2.1.comp hκ.2.1, fun p => (g1.2.2.1 _).trans (congrArg κ' (hκ.2.2.1 p)), ?_⟩
    rintro q ⟨k, hk⟩
    obtain ⟨r, rfl⟩ := g1.2.2.2 q ⟨κ k, hk⟩
    obtain ⟨t, rfl⟩ := hκ.2.2.2 r ⟨k, g1.1 (hk.trans (g1.2.2.1 r))⟩
    exact ⟨t, rfl⟩
  have hB' : BasesOver (φ.comp i) (j'.comp j) tie'.eW tie'.eO tie.eW tie.eO :=
    ⟨fun τ a => (g4.1 τ a).trans (congrArg j' (hB.1 τ a)), fun τ a w w' e =>
      (g4.2 τ a ⟨j w, ho.map_Vgen _ w.2⟩ w' e).trans (congrArg φ (hB.2 τ a w _ rfl))⟩
  obtain ⟨Cv, -, -, -, hC⟩ := hb E H D l Xo c Y S S' K ι Φ y K' ι' Φ' y' M M' 𝔐 𝔐₁ tie tie' _ _ (φ.comp i) (π ≫ h)
    (j'.comp j) d d' hκ' (fun q => (g2 _).trans (congrArg φ (hx q))) (g3.trans ho) hB' hd h1
  exact ⟨K', _, ι', _, Φ', _, y', M', Cv, 𝔐', Fl, hC.trans h4.symm⟩

theorem CoverExists.diag (hb : CoverExists) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type}
    [Field Φ] {y : (Σ k, ι k) → Φ} {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}
    (tie : FlagTie M 𝔐) {d : ℕ} (hd : 𝔐.IsCover d) :
    ∃ Cv : FlagCover M M, Cv.v = id ∧ d * Cv.deg = d ∧ Cv.deg = 1 := by
  obtain ⟨Cv, -, h1, -, h2⟩ := hb E H D l Xo c Y S S K ι Φ y K ι Φ y M M 𝔐 𝔐 tie tie id id (RingHom.id _) (𝟙 _)
    (AddMonoidHom.id _) d d ⟨Function.injective_id, Function.injective_id, fun _ => rfl, fun q _ => ⟨q, rfl⟩⟩
    (fun _ => rfl) (HodgeOver.refl 𝔐) (BasesOver.refl _ _) hd hd
  refine ⟨Cv, h1, h2, ?_⟩
  rw [FlagCover.deg, h1]
  exact IntermediateField.relfinrank_self _

end Chain

end GlobalTheory.CompanionTheory.Ar.PB
