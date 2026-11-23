import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.OmNatT

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

universe v u

theorem rep_unique {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : Rep a b z c) (h' : Rep a b z c') : c = c' := by
  obtain ⟨f, hf, e, hz⟩ := h
  obtain ⟨f', hf', e', hz'⟩ := h'
  have hff : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst hff
  exact e.trans e'.symm

section Span

variable (K A : Type) [CommRing K] [CommRing A] [Algebra K A]

theorem multi_mem {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {a : ℕ}
    (f : MultilinearMap A (fun _ : Fin a => M) N) (s : Set M) (hs : Submodule.span A s = ⊤) (S : Submodule A N)
    (h : ∀ v : Fin a → M, (∀ k, v k ∈ s) → f v ∈ S) (v : Fin a → M) : f v ∈ S := by
  classical
  have key : ∀ (t : Finset (Fin a)) (v : Fin a → M), (∀ k, k ∉ t → v k ∈ s) → f v ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun v hv => h v fun k => hv k (by simp)
    | insert i t hi ih =>
      intro v hv
      have hvi : v i ∈ Submodule.span A s := hs ▸ Submodule.mem_top
      have : ∀ x ∈ Submodule.span A s, f (Function.update v i x) ∈ S := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hxs =>
          refine ih _ fun k hk => ?_
          by_cases e : k = i
          · rw [e, Function.update_self]; exact hxs
          · rw [Function.update_of_ne e]
            exact hv k (by simp [e, hk])
        | zero => rw [f.map_update_zero]; exact S.zero_mem
        | add x y _ _ hx hy => rw [f.map_update_add]; exact S.add_mem hx hy
        | smul c x _ hx => rw [f.map_update_smul]; exact S.smul_mem _ hx
      simpa using this _ hvi
  exact key Finset.univ v fun k hk => (hk (Finset.mem_univ k)).elim

theorem span_form (a : ℕ) : Submodule.span K {ω : ⋀[A]^a Ω[A⁄K] | ∃ (g₀ : A) (g : Fin a → A), ω = CrystallineSemistableComparison.Onto.form K g₀ g} = ⊤ := by
  set S := Submodule.span K {ω : ⋀[A]^a Ω[A⁄K] | ∃ (g₀ : A) (g : Fin a → A), ω = CrystallineSemistableComparison.Onto.form K g₀ g} with hS
  have hsm : ∀ (c : A) x, x ∈ S → c • x ∈ S := by
    intro c x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, g, rfl⟩ := hx
      refine Submodule.subset_span ⟨c * g₀, g, ?_⟩
      simp only [CrystallineSemistableComparison.Onto.form, mul_smul]
    | zero => rw [smul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact S.add_mem hx hy
    | smul r x _ hx =>
      rw [← algebraMap_smul A r x, smul_comm, algebraMap_smul]
      exact S.smul_mem r hx
  let S' : Submodule A (⋀[A]^a Ω[A⁄K]) :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := hsm }
  have hι : ∀ v : Fin a → Ω[A⁄K], exteriorPower.ιMulti A a v ∈ S' := fun v =>
    multi_mem A (exteriorPower.ιMulti A a (M := Ω[A⁄K])).toMultilinearMap (Set.range (KaehlerDifferential.D K A))
      (KaehlerDifferential.span_range_derivation K A) S' (fun v hv => by
        choose g hg using hv
        refine Submodule.subset_span ⟨1, g, ?_⟩
        have e : v = fun k => KaehlerDifferential.D K A (g k) := (funext hg).symm
        simp only [CrystallineSemistableComparison.Onto.form, one_smul]
        rw [← e]
        rfl) v
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A a (M := Ω[A⁄K]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  have : Submodule.span A (Set.range (exteriorPower.ιMulti A a (M := Ω[A⁄K]))) ≤ S' :=
    Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact hι v)
  exact this hx

end Span

section Mom

variable {R R' B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing R'] [CommRing B'] [Algebra R' B']
  {σ : R →+* R'} {α : B →+* B'}

theorem mOm_form (h : SemiHom σ α) {a : ℕ} (g₀ : B) (g : Fin a → B) :
    h.mOm a (CrystallineSemistableComparison.Onto.form R g₀ g) = CrystallineSemistableComparison.Onto.form R' (α g₀) fun k => α (g k) := by
  unfold CrystallineSemistableComparison.Onto.form
  rw [h.mOm_smul]
  congr 1
  refine Subtype.ext ?_
  rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext k
  simp

end Mom

section Pull

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def outL (q : X ⟶ Spec (CommRingCat.of K)) : LiftsT q where
  v T g := Quotient.out (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Ideal.Quotient.mk_out _

variable {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

def uS (u : X ⟶ Y) : Γ(Y, ⊤) →+* Γ(X, ⊤) := (u.appLE ⊤ ⊤ (by simp)).hom

theorem ev_pull (u : X ⟶ Y) (hu : u ≫ p = q) (T : Thick (smFun X q)) (g : Γ(Y, ⊤)) :
    ev (γ := dividedPowersBot K) (p := 0) (q := p) (κ := Ideal.Quotient.mk ⊥) ((smS u hu).G.obj T) (inTop p _) g =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) (uS u g) := by
  change (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).hom.hom (((pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T ≫ u).appLE ⊤ ⊤ _).hom g) =
    (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).hom.hom (((pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T).appLE ⊤ ⊤ _).hom ((u.appLE ⊤ ⊤ (by simp)).hom g))
  congr 1
  rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ ⊤ (by simp) (by simp)]
  rfl

theorem out_pull (u : X ⟶ Y) (hu : u ≫ p = q) (T : Thick (smFun X q)) (g : Γ(Y, ⊤)) :
    (outL p).v ((smS u hu).G.obj T) g = (outL q).v T (uS u g) :=
  congrArg Quotient.out (ev_pull u hu T g)

theorem form_pull (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ} (g₀ : Γ(Y, ⊤)) (g : Fin a → Γ(Y, ⊤))
    (s : ComposableArrows (Thick (smFun X q)) a) :
    (outL q).form (uS u g₀) (fun k => uS u (g k)) s = (outL p).form g₀ g (s ⋙ (smS u hu).G) := by
  unfold LiftsT.form
  refine congrArg₂ (· * ·) (out_pull u hu _ g₀).symm (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg₂ (· - ·) (congrArg _ (out_pull u hu _ (g k)).symm) (congrArg _ (out_pull u hu _ (g k)).symm)

theorem rep_pull (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ}
    {z : ∀ s : ComposableArrows (Thick (smFun Y p)) a, (s.obj (Fin.last a)).B}
    {z' : ∀ s : ComposableArrows (Thick (smFun X q)) a, (s.obj (Fin.last a)).B}
    (hz : ∀ s, z' s = z (s ⋙ (smS u hu).G)) {c : Hdg p a a}
    (h : Rep (thFil (smFun Y p) (a : ℤ)) (thFil (smFun Y p) ((a : ℤ) + 1)) z (show CH.H (grT (smFun Y p) a) a from c)) :
    Rep (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1)) z'
      (show CH.H (grT (smFun X q) a) a from pullH u hu a a c) := by
  obtain ⟨f, hf, e, hfz⟩ := h
  let m : CH.Mor (grT (smFun Y p) a) (grT (smFun X q) a) (RingHom.id K) :=
    (smS u hu).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ)) (b' := thFil _ ((a : ℤ) + 1))
      (fun _ _ hx => hx) fun _ _ hx => hx
  have hd : CH.d (grT (smFun X q) a) a (m.pullC a f) = 0 := by
    rw [m.d_pullC, hf, map_zero]
  refine ⟨m.pullC a f, hd, ?_, fun s => ?_⟩
  · change m.pull a c = _
    have : c = (CH.cx (grT (smFun Y p) a)).cls f hf := e
    rw [this]
    exact CrystallineSemistableComparison.P.mapH_cls m.hom a f hf hd
  · rw [hz s]
    exact congrArg (Ideal.quotientMap _ ((smS u hu).ρ _) _) (hfz (s ⋙ (smS u hu).G))

end Pull

section Main

variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

theorem res_pull_form (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ} (g₀ : Γ(Y, ⊤)) (g : Fin a → Γ(Y, ⊤)) :
    formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (gForm p g₀ g)) =
      gForm q (uS u g₀) fun k => uS u (g k) := by
  have e1 : formPull hu ⊤ a (gForm p g₀ g) = CrystallineSemistableComparison.Onto.form K (A := Sec q (u ⁻¹ᵁ ⊤)) (appSec p q u ⊤ g₀)
      fun k => appSec p q u ⊤ (g k) := mOm_form (semiHom_appSec hu ⊤) g₀ g
  rw [e1]
  exact mOm_form (SemiHom.of_algHom (Sec.res q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp))) _ _

end Main

theorem pull_nat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)) := by
  intro K _ X Y q p u hu a e e' he he' x
  have key : ∀ ω : OmU p ⊤ a, e (pullH u hu a a (e'.symm ω)) =
      formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a ω) := by
    intro ω
    have hω : ω ∈ Submodule.span K {ω : ⋀[Sec p ⊤]^a Ω[Sec p ⊤⁄K] | ∃ (g₀ : Sec p ⊤) (g : Fin a → Sec p ⊤),
        ω = CrystallineSemistableComparison.Onto.form K g₀ g} := by
      rw [span_form]; trivial
    induction hω using Submodule.span_induction with
    | mem ω hω =>
      obtain ⟨g₀, g, rfl⟩ := hω
      have h1 := he' g₀ g (outL p)
      have h2 := he (uS u g₀) (fun k => uS u (g k)) (outL q)
      have h3 := rep_pull u hu (fun s => form_pull u hu g₀ g s) h1
      have h4 : pullH u hu a a (e'.symm (gForm p g₀ g)) = e.symm (gForm q (uS u g₀) fun k => uS u (g k)) :=
        rep_unique h3 h2
      refine Eq.trans ?_ (res_pull_form u hu g₀ g).symm
      change e (pullH u hu a a (e'.symm (gForm p g₀ g))) = _
      rw [h4, LinearEquiv.apply_symm_apply]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul r x _ hx =>
      simp only [map_smul, hx]
  simpa using key (e' x)

end GlobalTheory.CompanionTheory.OmNatT
