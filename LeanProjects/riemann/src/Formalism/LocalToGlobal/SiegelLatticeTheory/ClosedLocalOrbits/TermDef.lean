import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.TermDef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def DCRel (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F₁ F₂ : LFlag S r T') : Prop :=
  ∃ n ∈ NLam Λ F, ∃ m ∈ NLam Λ F₁,
    (∀ a, frame F₂ a = n (m (frame F₁ a))) ∧ F₂.zt = n (m F₁.zt)

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop)

abbrev Carrier : Type := {F' : LFlag S r T' // P F'}

def Rel (x y : Carrier P) : Prop := DCRel Λ F x.1 y.1

def TermQ : Type := Quot (Rel Λ F P)

def mk (x : Carrier P) : TermQ Λ F P := Quot.mk _ x

def Rep (t : TermQ Λ F P) (F' : LFlag S r T') : Prop := ∃ h : P F', mk Λ F P ⟨F', h⟩ = t

def Gt (t : TermQ Λ F P) : E := Gval F (Quot.out t).1

def IsRel (K : Type) [Field K] [Algebra K E] (t : TermQ Λ F P) : Prop :=
  ∃ F', Rep Λ F P t F' ∧ Relevant K F.fl F'.fl

def IsGen (g : ℕ) (t : TermQ Λ F P) : Prop := ∃ F', Rep Λ F P t F' ∧ IsGeneric Λ g F F'

def IsFeqF (t : TermQ Λ F P) : Prop :=
  ∃ F', Rep Λ F P t F' ∧ ∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame F' a

def AtPt (t : TermQ Λ F P) (w : Point E (r + 1)) : Prop :=
  ∃ F', Rep Λ F P t F' ∧ Gval F F' ≠ 0 ∧ IsInCell (ZhatOM (ZhatL F F')) w

def EqIff : Prop := ∀ x y : Carrier P, mk Λ F P x = mk Λ F P y ↔ Rel Λ F P x y

def Stable : Prop := ∀ (x : Carrier P) (F₂ : LFlag S r T'), DCRel Λ F x.1 F₂ → P F₂

def GFun : Prop := ∀ x y : Carrier P, Rel Λ F P x y → Gval F x.1 = Gval F y.1

def CellFun : Prop := ∀ x y : Carrier P, Rel Λ F P x y → ∀ w : Point E (r + 1),
  (IsInCell (ZhatOM (ZhatL F x.1)) w ↔ IsInCell (ZhatOM (ZhatL F y.1)) w)

def RelFun (K : Type) [Field K] [Algebra K E] : Prop := ∀ x y : Carrier P, Rel Λ F P x y →
  (Relevant K F.fl x.1.fl ↔ Relevant K F.fl y.1.fl)

def GenFun (g : ℕ) : Prop := ∀ x y : Carrier P, Rel Λ F P x y →
  (IsGeneric Λ g F x.1 ↔ IsGeneric Λ g F y.1)

def FeqFFun : Prop := ∀ x y : Carrier P, Rel Λ F P x y →
  ((∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame x.1 a) ↔ (∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame y.1 a))

theorem one_mem_NLam {T₀ : E} (F₀ : LFlag S r T₀) : (1 : S.V ≃ₗ[E] S.V) ∈ NLam Λ F₀ := by
  simp only [NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨one_mem _, ?_⟩, fun j x _ => ?_, fun x _ => ?_⟩
  · unfold Formalism.HermitianLatticesTheory.gmap
    ext v
    simp
  · rw [show (1 : S.V ≃ₗ[E] S.V) x = x from rfl, sub_self]
    exact zero_mem _
  · rw [show (1 : S.V ≃ₗ[E] S.V) x = x from rfl, sub_self]
    exact zero_mem _

theorem dcrel_refl (F₁ : LFlag S r T') : DCRel Λ F F₁ F₁ := by
  unfold DCRel
  exact ⟨1, one_mem_NLam Λ F, 1, one_mem_NLam Λ F₁, fun _ => rfl, rfl⟩

variable {Λ F P}

theorem const_of_mk {β : Sort*} (f : Carrier P → β) (hf : ∀ x y, Rel Λ F P x y → f x = f y)
    {x y : Carrier P} (h : mk Λ F P x = mk Λ F P y) : f x = f y := by
  exact congrArg (Quot.lift f hf) h

theorem rep_mk (x : Carrier P) : Rep Λ F P (mk Λ F P x) x.1 := by
  unfold Rep
  exact ⟨x.2, rfl⟩

theorem Gt_mk (hG : GFun Λ F P) (x : Carrier P) : Gt Λ F P (mk Λ F P x) = Gval F x.1 := by
  exact const_of_mk (fun y : Carrier P => Gval F y.1) hG (Quot.out_eq (mk Λ F P x))

theorem isRel_mk (K : Type) [Field K] [Algebra K E] (hR : RelFun Λ F P K) (x : Carrier P) :
    IsRel Λ F P K (mk Λ F P x) ↔ Relevant K F.fl x.1.fl := by
  unfold IsRel
  constructor
  · rintro ⟨F', ⟨h, e⟩, hr⟩
    have e' := const_of_mk (fun y : Carrier P => Relevant K F.fl y.1.fl) (fun a b r => propext (hR a b r)) e
    exact cast e' hr
  · intro hr
    exact ⟨x.1, rep_mk x, hr⟩

theorem isGen_mk (g : ℕ) (hR : GenFun Λ F P g) (x : Carrier P) :
    IsGen Λ F P g (mk Λ F P x) ↔ IsGeneric Λ g F x.1 := by
  unfold IsGen
  constructor
  · rintro ⟨F', ⟨h, e⟩, hr⟩
    have e' := const_of_mk (fun y : Carrier P => IsGeneric Λ g F y.1) (fun a b r => propext (hR a b r)) e
    exact cast e' hr
  · intro hr
    exact ⟨x.1, rep_mk x, hr⟩

theorem isFeqF_mk (hR : FeqFFun Λ F P) (x : Carrier P) :
    IsFeqF Λ F P (mk Λ F P x) ↔ ∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame x.1 a := by
  unfold IsFeqF
  constructor
  · rintro ⟨F', ⟨h, e⟩, hr⟩
    have e' := const_of_mk (fun y : Carrier P => ∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame y.1 a)
      (fun a b r => propext (hR a b r)) e
    exact cast e' hr
  · intro hr
    exact ⟨x.1, rep_mk x, hr⟩

theorem atPt_mk (hG : GFun Λ F P) (hC : CellFun Λ F P) (x : Carrier P) (w : Point E (r + 1)) :
    AtPt Λ F P (mk Λ F P x) w ↔ Gval F x.1 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL F x.1)) w := by
  unfold AtPt
  constructor
  · rintro ⟨F', ⟨h, e⟩, hg, hc⟩
    have e1 := const_of_mk (fun y : Carrier P => Gval F y.1) hG e
    have e2 := const_of_mk (fun y : Carrier P => IsInCell (ZhatOM (ZhatL F y.1)) w)
      (fun a b r => propext (hC a b r w)) e
    exact ⟨fun h0 => hg (e1.trans h0), cast e2 hc⟩
  · rintro ⟨hg, hc⟩
    exact ⟨x.1, rep_mk x, hg, hc⟩

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def PD (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T : D.host.E} (F : LFlag (hS D) D.R.rS T) (u' : D.what₂.Word)
    (F' : LFlag (hS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) : Prop :=
  IsLift Λ F' ∧ IsAdmissible Λ (gS D) F F' ∧ FrameOK D Λ F'

abbrev TermsOf (u' : D.what₂.Word) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Type :=
  TermQ Λ (lf D F0) (PD D Λ (lf D F0) u')

structure Term (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) where
  lam : Submodule (𝓞 D.host.E) (VS D).V
  mem : lam ∈ what₂
  cls : TermsOf D u' F0 lam

variable {D}

section Attr

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def Term.G (t : Term D u u' F0 what₂) : D.host.E := Gt _ _ _ t.cls

def Term.relevant (t : Term D u u' F0 what₂) : Prop := IsRel _ _ _ D.host.F t.cls

def Term.generic (t : Term D u u' F0 what₂) : Prop := IsGen _ _ _ (gS D) t.cls

def Term.FeqF (t : Term D u u' F0 what₂) : Prop := IsFeqF _ _ _ t.cls

def Term.atPt (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) : Prop := AtPt _ _ _ t.cls w

end Attr

variable (D)

def TermEqIff (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → EqIff Λ (lf D F0) (PD D Λ (lf D F0) u')

def TermStable (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → Stable Λ (lf D F0) (PD D Λ (lf D F0) u')

def TermFun (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ →
      GFun Λ (lf D F0) (PD D Λ (lf D F0) u') ∧ CellFun Λ (lf D F0) (PD D Λ (lf D F0) u') ∧
      RelFun Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F ∧
      GenFun Λ (lf D F0) (PD D Λ (lf D F0) u') (gS D) ∧ FeqFFun Λ (lf D F0) (PD D Λ (lf D F0) u')

def TermsAtFinite (u u' : D.what₂.Word) : Prop :=
  (VS D).SigOK →
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ w : Point D.host.E (D.R.rS + 1),
      {t : TermsOf D u' F0 Λ | AtPt Λ (lf D F0) (PD D Λ (lf D F0) u') t w}.Finite

variable {D}

def Term.toSig {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (t : Term D u u' F0 what₂) :
    Σ Λ : {Λ // Λ ∈ what₂}, TermsOf D u' F0 Λ.1 := ⟨⟨t.lam, t.mem⟩, t.cls⟩

theorem Term.toSig_injective {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} :
    Function.Injective (Term.toSig (u' := u') (F0 := F0) (what₂ := what₂)) := by
  intro t1 t2 h
  cases t1
  cases t2
  cases h
  rfl

theorem term_atPt_finite {u u' : D.what₂.Word} (hfin : TermsAtFinite D u u') (hsig : (VS D).SigOK)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (hrows : IsRowReps D F0 what₂) (w : Point D.host.E (D.R.rS + 1)) :
    {t : Term D u u' F0 what₂ | t.atPt w}.Finite := by
  have hfin' : ∀ Λ : {Λ // Λ ∈ what₂},
      {c : TermsOf D u' F0 Λ.1 | AtPt Λ.1 (lf D F0) (PD D Λ.1 (lf D F0) u') c w}.Finite :=
    fun Λ => hfin hsig F0 Λ.1 (hrows.1 Λ.1 Λ.2) w
  refine (Set.finite_iUnion fun Λ : {Λ // Λ ∈ what₂} =>
    (hfin' Λ).image (fun c => (⟨Λ.1, Λ.2, c⟩ : Term D u u' F0 what₂))).subset ?_
  rintro ⟨l, m, c⟩ ht
  exact Set.mem_iUnion.2 ⟨⟨l, m⟩, c, ht, rfl⟩

theorem pd_self {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) :
    PD D Λ (lf D F0) u (lf D F0) := by
  obtain ⟨_, hfix, hX⟩ := hΛ
  obtain ⟨_, _, hlift, hconv⟩ := hfix
  unfold PD
  refine ⟨hlift, ?_, ?_⟩
  · unfold IsAdmissible AdmWit
    refine ⟨1, fun a b hab => Matrix.one_apply_ne hab.ne', fun a => Matrix.one_apply_eq a, fun b => ?_⟩
    have h0 : frameAct (frame (lf D F0)) (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) b =
        frame (lf D F0) b := by
      unfold frameAct
      rw [Finset.sum_eq_single b]
      · simp
      · intro a _ hab
        simp [Matrix.one_apply_ne hab]
      · intro h
        exact absurd (Finset.mem_univ b) h
    rw [h0, sub_self]
    unfold ModG
    intro P _
    exact zero_mem _
  · unfold FrameOK
    exact ⟨hconv, hX⟩

def idTerm {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hrows : IsRowReps D F0 what₂)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : Term D u u F0 what₂ :=
  ⟨Λ, hΛ, mk _ _ _ ⟨lf D F0, pd_self F0 Λ (hrows.1 Λ hΛ)⟩⟩

def TermFeqFIff (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : IsRowLat D F0 Λ) (t : TermsOf D u F0 Λ),
      IsFeqF Λ (lf D F0) (PD D Λ (lf D F0) u) t ↔ t = mk _ _ _ ⟨lf D F0, pd_self F0 Λ hΛ⟩

theorem idTerm_FeqF {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hrows : IsRowReps D F0 what₂)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : (idTerm F0 what₂ hrows Λ hΛ).FeqF := by
  unfold Term.FeqF IsFeqF
  exact ⟨lf D F0, rep_mk _, 1, one_mem_NLam _ _, fun _ => rfl⟩

theorem termFeqFIff_holds (D : D7) (u : D.what₂.Word) : TermFeqFIff D u := by
  intro F0 Λ hΛ t
  unfold IsFeqF
  constructor
  · rintro ⟨F', ⟨h, rfl⟩, n, hn, hfr⟩
    symm
    apply Quot.sound
    unfold Rel DCRel
    have hz : F'.zt = F'.fl.z := by
      obtain ⟨⟨_, hz⟩, _⟩ := h
      exact hz
    have hlast := hfr (Fin.last _)
    simp only [frame, FlagG.fvec, Fin.snoc_last] at hlast
    refine ⟨n, hn, 1, one_mem_NLam _ _, fun a => (hfr a).symm, ?_⟩
    rw [hz]
    exact hlast.symm
  · rintro rfl
    exact ⟨lf D F0, rep_mk _, 1, one_mem_NLam _ _, fun _ => rfl⟩

end D7

end Formalism.L2.SG.TermDef
