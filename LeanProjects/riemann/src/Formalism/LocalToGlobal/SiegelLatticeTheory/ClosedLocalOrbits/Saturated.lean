import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Saturated

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem isom_apply {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) :
    S.hT (β x) (β y) = S.hT x y := by
  exact hβ x y

theorem mem_gmap_iff (β : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.gmap β L ↔ β.symm x ∈ L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : β y = x := hyx
    rw [← hyx', LinearEquiv.symm_apply_apply]
    exact hy
  · intro h
    exact ⟨β.symm x, h, β.apply_symm_apply x⟩

def mapFlag (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T : E} (F : FlagG S r T) : FlagG S r T where
  e a := β (F.e a)
  z := β F.z
  e_indep := F.e_indep.map' (β : S.V →ₗ[E] S.V) β.ker
  e_iso a b := by rw [isom_apply hβ]; exact F.e_iso a b
  z_orth a := by rw [isom_apply hβ]; exact F.z_orth a
  z_norm := by rw [isom_apply hβ]; exact F.z_norm

def mapL (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T : E} (F : LFlag S r T) : LFlag S r T :=
  ⟨mapFlag β hβ F.fl, β F.zt⟩

theorem fvec_mapFlag (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T : E} (F : FlagG S r T) :
    (mapFlag β hβ F).fvec = fun a => β (F.fvec a) := by
  funext a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

theorem frame_mapL (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T : E} (F : LFlag S r T)
    (a : Fin (r + 1)) : frame (mapL β hβ F) a = β (frame F a) := by
  exact congrFun (fvec_mapFlag β hβ F.fl) a

theorem zhat_mapL (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T T' : E} (F : LFlag S r T)
    (F' : LFlag S r T') : ZhatL (mapL β hβ F) (mapL β hβ F') = ZhatL F F' := by
  show Zhat (mapFlag β hβ F.fl) (mapFlag β hβ F'.fl) = Zhat F.fl F'.fl
  ext a b
  simp only [Zhat, brS, fvec_mapFlag, isom_apply hβ]

theorem gval_mapL (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T T' : E} (F : LFlag S r T)
    (F' : LFlag S r T') : Gval (mapL β hβ F) (mapL β hβ F') = Gval F F' := by
  have hz : Zhat (mapFlag β hβ F.fl) (mapFlag β hβ F'.fl) = Zhat F.fl F'.fl := zhat_mapL β hβ F F'
  show Gflag (mapFlag β hβ F.fl) (mapFlag β hβ F'.fl) = Gflag F.fl F'.fl
  simp only [Gflag, Dl, hz]

theorem mapL_mul (β γ : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    {T : E} (F : LFlag S r T) :
    mapL (β * γ) (Subgroup.mul_mem _ hβ hγ) F = mapL β hβ (mapL γ hγ F) := rfl

private theorem flag_ext_lemma {T : E} {F₁ F₂ : FlagG S r T} (he : F₁.e = F₂.e) (hz : F₁.z = F₂.z) :
    F₁ = F₂ := by
  obtain ⟨e₁, z₁, _, _, _, _⟩ := F₁
  obtain ⟨e₂, z₂, _, _, _, _⟩ := F₂
  dsimp only at he hz
  subst he hz
  rfl

private theorem lflag_ext_lemma_2 {T : E} {F₁ F₂ : LFlag S r T} (h1 : F₁.fl = F₂.fl) (h2 : F₁.zt = F₂.zt) :
    F₁ = F₂ := by
  obtain ⟨f₁, z₁⟩ := F₁
  obtain ⟨f₂, z₂⟩ := F₂
  dsimp only at h1 h2
  subst h1 h2
  rfl

theorem mapL_eq_self (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T : E} (F : LFlag S r T)
    (hf : ∀ a, β (frame F a) = frame F a) (hz : β F.zt = F.zt) : mapL β hβ F = F := by
  have he : ∀ a, β (F.fl.e a) = F.fl.e a := fun a => by
    have h := hf (Fin.castSucc a)
    simpa [frame, FlagG.fvec] using h
  have hz' : β F.fl.z = F.fl.z := by
    have h := hf (Fin.last r)
    simpa [frame, FlagG.fvec] using h
  apply lflag_ext_lemma_2
  · apply flag_ext_lemma
    · funext a
      exact he a
    · exact hz'
  · exact hz

def AutF {T : E} (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) : Set (S.V ≃ₗ[E] S.V) :=
  {β | IsAutLam S Λ β ∧ (∀ a, β (frame F a) = frame F a) ∧ β F.zt = F.zt}

theorem mem_AutF {T : E} {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {β : S.V ≃ₗ[E] S.V} :
    β ∈ AutF Λ F ↔ IsAutLam S Λ β ∧ (∀ a, β (frame F a) = frame F a) ∧ β F.zt = F.zt := by
  exact Iff.rfl

variable {T T' : E} {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T}

theorem AutF.isom (β : AutF Λ F) : (β : S.V ≃ₗ[E] S.V) ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  exact (mem_AutF.mp β.2).1.1

theorem AutF.lam (β : AutF Λ F) : Formalism.HermitianLatticesTheory.gmap (β : S.V ≃ₗ[E] S.V) Λ = Λ := by
  exact (mem_AutF.mp β.2).1.2

def act (β : AutF Λ F) (F' : LFlag S r T') : LFlag S r T' := mapL β.1 (AutF.isom β) F'

theorem one_mem_AutF : (1 : S.V ≃ₗ[E] S.V) ∈ AutF Λ F := by
  refine mem_AutF.mpr (And.intro (And.intro (Subgroup.one_mem _) ?_) (And.intro (fun a => rfl) rfl))
  ext x
  rw [mem_gmap_iff]
  exact Iff.rfl

theorem act_one (F' : LFlag S r T') : act (⟨1, one_mem_AutF⟩ : AutF Λ F) F' = F' := by
  exact mapL_eq_self _ _ _ (fun _ => rfl) rfl

theorem inv_mem_AutF' {β : S.V ≃ₗ[E] S.V} (h : β ∈ AutF Λ F) : β⁻¹ ∈ AutF Λ F := by
  obtain ⟨⟨hiso, hlam⟩, hf, hz⟩ := mem_AutF.mp h
  refine mem_AutF.mpr (And.intro (And.intro (Subgroup.inv_mem _ hiso) ?_) (And.intro (fun a => ?_) ?_))
  · ext x
    rw [mem_gmap_iff]
    show β x ∈ Λ ↔ x ∈ Λ
    conv_lhs => rw [← hlam]
    rw [mem_gmap_iff, LinearEquiv.symm_apply_apply]
  · show β.symm (frame F a) = frame F a
    rw [LinearEquiv.symm_apply_eq]
    exact (hf a).symm
  · show β.symm F.zt = F.zt
    rw [LinearEquiv.symm_apply_eq]
    exact hz.symm

def IsoInv (Q : Submodule (𝓞 E) S.V → LFlag S r T → LFlag S r T' → Prop) : Prop :=
  ∀ (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (F' : LFlag S r T'), Q (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') ↔ Q Λ F F'

variable (Λ F) in

def Inv (Q : LFlag S r T' → Prop) : Prop := ∀ (β : AutF Λ F) (F' : LFlag S r T'), Q (act β F') ↔ Q F'

theorem inv_of_isoInv {Q : Submodule (𝓞 E) S.V → LFlag S r T → LFlag S r T' → Prop} (hQ : IsoInv Q) :
    Inv Λ F (Q Λ F) := by
  intro β F'
  have h := hQ β.1 (AutF.isom β) Λ F F'
  rw [AutF.lam β, mapL_eq_self β.1 (AutF.isom β) F (mem_AutF.mp β.2).2.1 (mem_AutF.mp β.2).2.2] at h
  exact h

theorem gval_act (β : AutF Λ F) (F' : LFlag S r T') : Gval F (act β F') = Gval F F' := by
  have h := gval_mapL β.1 (AutF.isom β) F F'
  rw [mapL_eq_self β.1 (AutF.isom β) F (mem_AutF.mp β.2).2.1 (mem_AutF.mp β.2).2.2] at h
  exact h

variable (Λ) in

def IotaG (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') (l' l : S.V) : Prop :=
  l' ∈ Lrep Λ F' ∧ l ∈ Lrep Λ F ∧ l - l' ∈ NgX Λ g F F'

variable (Λ) in

def IotaRestrictionOrthogonal (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') (l' l : S.V) : Prop :=
  IotaG Λ g F F' l' l ∧ S.hT F'.fl.z l' = 0 ∧ S.hT F.fl.z l = 0

variable (Λ) in

def BBneP (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  (((g : 𝓞 E) ∈ P.asIdeal) → ∀ ξ, AdmWit Λ g F F' ξ →
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ F F') ≠
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ))) ∧
  (((g : 𝓞 E) ∉ P.asIdeal) →
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ F F') ≠ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')))

theorem not_BBneP_of_generic {g : ℕ} {F' : LFlag S r T'} (h : IsGeneric Λ g F F')
    (P : HeightOneSpectrum (𝓞 E)) : ¬ BBneP Λ g F F' P := by
  rintro ⟨h1, h2⟩
  obtain ⟨ξ, hξ, hP⟩ := h
  by_cases hg : ((g : 𝓞 E) ∈ P.asIdeal)
  · exact h1 hg ξ hξ ((hP P).1 hg)
  · exact h2 hg ((hP P).2 hg)

variable (Λ F) in

def MplusIndep (g : ℕ) (F' : LFlag S r T') : Prop :=
  IsLift Λ F → IsFixedConv Λ g F → ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) → ∀ ξ₁ ξ₂,
    AdmWit Λ g F F' ξ₁ → AdmWit Λ g F F' ξ₂ →
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ₁) =
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ₂))

theorem generic_of_not_BBneP {g : ℕ} {F' : LFlag S r T'} (hI : MplusIndep Λ F g F') (hL : IsLift Λ F)
    (hF : IsFixedConv Λ g F)
    (hadm : IsAdmissible Λ g F F') (h : ∀ P, ¬ BBneP Λ g F F' P) : IsGeneric Λ g F F' := by
  obtain ⟨ξ, hξ⟩ := hadm
  refine Exists.intro ξ (And.intro hξ (fun P => And.intro (fun hg => ?_) (fun hg => ?_)))
  · by_contra hne
    exact h P (And.intro (fun _ ξ' hξ' heq => hne (heq.trans (hI hL hF P hg ξ' ξ hξ' hξ))) (fun hg' => absurd hg hg'))
  · by_contra hne
    exact h P (And.intro (fun hg' => absurd hg' hg) (fun _ => hne))

variable (S r) in

def GenIso (g : ℕ) : Prop :=
  ∀ T T' : E, IsoInv (S := S) (r := r) (T := T) (T' := T') (fun Λ F F' => IsGeneric Λ g F F')

variable (S r) in

def RelIso (K : Type) [Field K] [Algebra K E] : Prop :=
  ∀ T T' : E, IsoInv (S := S) (r := r) (T := T) (T' := T') (fun _ F F' => Relevant K F.fl F'.fl)

variable (S r) in

def FeqFIso : Prop :=
  ∀ T T' : E, IsoInv (S := S) (r := r) (T := T) (T' := T')
    (fun Λ F F' => ∃ n ∈ NLam Λ F, ∀ a, n (frame F a) = frame F' a)

variable (S r) in

def BBIso (g : ℕ) : Prop :=
  ∀ (T T' : E) (P : HeightOneSpectrum (𝓞 E)),
    IsoInv (S := S) (r := r) (T := T) (T' := T') (fun Λ F F' => BBneP Λ g F F' P)

variable (S r) in

def IotaIso (g : ℕ) : Prop :=
  ∀ (T T' : E) (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' : LFlag S r T') (l' l : S.V),
    IotaG (Formalism.HermitianLatticesTheory.gmap β Λ) g (mapL β hβ F) (mapL β hβ F') (β l') (β l) ↔ IotaG Λ g F F' l' l

variable (S r) in

def DCIso : Prop :=
  ∀ (T T' : E) (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F₁ F₂ : LFlag S r T'),
    DCRel (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F₁) (mapL β hβ F₂) ↔ DCRel Λ F F₁ F₂

variable (S r) in

def IotaZ (g : ℕ) : Prop :=
  ∀ (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'),
    IsLift Λ F → IsLift Λ F' → IsAdmissible Λ g F F' → IotaG Λ g F F' F'.fl.z F.fl.z

variable {P : LFlag S r T' → Prop}

variable (Λ F P) in

def IsSat (TT : Set (TermQ Λ F P)) : Prop :=
  ∀ (β : AutF Λ F) (x : Carrier P) (h : P (act β x.1)), mk Λ F P x ∈ TT → mk Λ F P ⟨act β x.1, h⟩ ∈ TT

variable (Λ F P) in

def famOf (Q : LFlag S r T' → Prop) : Set (TermQ Λ F P) := {t | ∃ F', Rep Λ F P t F' ∧ Q F'}

variable (Λ F P) in

def QFun (Q : LFlag S r T' → Prop) : Prop := ∀ x y : Carrier P, Rel Λ F P x y → (Q x.1 ↔ Q y.1)

theorem mem_famOf_mk {Q : LFlag S r T' → Prop} (hF : QFun Λ F P Q) (x : Carrier P) :
    mk Λ F P x ∈ famOf Λ F P Q ↔ Q x.1 := by
  constructor
  · rintro ⟨F', ⟨h, e⟩, hq⟩
    have he : Q F' = Q x.1 :=
      congrArg (Quot.lift (fun y : Carrier P => Q y.1) (fun a b hab => propext (hF a b hab))) e
    exact he ▸ hq
  · intro hq
    exact Exists.intro x.1 (And.intro (Exists.intro x.2 rfl) hq)

theorem sat_famOf {Q : LFlag S r T' → Prop} (hQ : Inv Λ F Q) (hF : QFun Λ F P Q) :
    IsSat Λ F P (famOf Λ F P Q) := by
  intro β x h hx
  rw [mem_famOf_mk hF] at hx ⊢
  exact (hQ β x.1).mpr hx

theorem sat_famOf_compl {Q : LFlag S r T' → Prop} (hQ : Inv Λ F Q) (hF : QFun Λ F P Q) :
    IsSat Λ F P (famOf Λ F P Q)ᶜ := by
  intro β x h hx
  rw [Set.mem_compl_iff, mem_famOf_mk hF] at hx ⊢
  exact fun hq => hx ((hQ β x.1).mp hq)

private theorem gt_mk_lemma_3 (hG : GFun Λ F P) (x : Carrier P) : Gt Λ F P (mk Λ F P x) = Gval F x.1 :=
  congrArg (Quot.lift (fun y : Carrier P => Gval F y.1) hG) (Quot.out_eq (mk Λ F P x))

theorem saturated_g_zero (hG : GFun Λ F P) : IsSat Λ F P {t | Gt Λ F P t = 0} := by
  intro β x hp hx
  have hx' : Gval F x.1 = 0 := by
    rw [← gt_mk_lemma_3 hG]
    exact hx
  show Gt Λ F P (mk Λ F P ⟨act β x.1, hp⟩) = 0
  rw [gt_mk_lemma_3 hG]
  show Gval F (act β x.1) = 0
  rw [gval_act]
  exact hx'

theorem sat_Gne (hG : GFun Λ F P) : IsSat Λ F P {t | Gt Λ F P t ≠ 0} := by
  intro β x hp hx
  have hx' : Gval F x.1 ≠ 0 := by
    rw [← gt_mk_lemma_3 hG]
    exact hx
  show Gt Λ F P (mk Λ F P ⟨act β x.1, hp⟩) ≠ 0
  rw [gt_mk_lemma_3 hG]
  show Gval F (act β x.1) ≠ 0
  rw [gval_act]
  exact hx'

theorem sat_gen {g : ℕ} (hI : GenIso S r g) (hF : GenFun Λ F P g) :
    IsSat Λ F P {t | IsGen Λ F P g t} ∧ IsSat Λ F P {t | ¬ IsGen Λ F P g t} := by
  exact ⟨sat_famOf (inv_of_isoInv (hI _ _)) hF, sat_famOf_compl (inv_of_isoInv (hI _ _)) hF⟩

theorem sat_rel {K : Type} [Field K] [Algebra K E] (hI : RelIso S r K) (hF : RelFun Λ F P K) :
    IsSat Λ F P {t | IsRel Λ F P K t} ∧ IsSat Λ F P {t | ¬ IsRel Λ F P K t} := by
  exact ⟨sat_famOf (inv_of_isoInv (hI _ _)) hF, sat_famOf_compl (inv_of_isoInv (hI _ _)) hF⟩

theorem sat_feqF (hI : FeqFIso S r) (hF : FeqFFun Λ F P) :
    IsSat Λ F P {t | IsFeqF Λ F P t} ∧ IsSat Λ F P {t | ¬ IsFeqF Λ F P t} := by
  exact ⟨sat_famOf (inv_of_isoInv (hI _ _)) hF, sat_famOf_compl (inv_of_isoInv (hI _ _)) hF⟩

def latSpan (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ aa a ∧ y = x • v a}

def IsSplitBy (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (F0 : FlagG S r T)
    (Λ : Submodule (𝓞 E) S.V) : Prop :=
  ∃ (f : Fin r → S.V) (L : Submodule (𝓞 E) S.V),
    (∀ a b, S.hT (f a) (f b) = 0) ∧ (∀ a b, S.hT (F0.e a) (f b) = if a = b then 1 else 0) ∧
    (∀ x ∈ L, ∀ a, S.hT (F0.e a) x = 0 ∧ S.hT (f a) x = 0) ∧ F0.z ∈ L ∧
    Λ = latSpan aa F0.e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def BBneF (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (p : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ P : HeightOneSpectrum (𝓞 D.host.E),
    P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal ∧ BBneP Λ (gS D) F F' P

def PDIso : Prop :=
  ∀ (u' : D.what₂.Word) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)),
    PD D (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) u' (mapL β hβ F') ↔ PD D Λ F u' F'

def BBFun (u u' : D.what₂.Word) : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D F0 Λ → ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      QFun Λ (lf D F0) (PD D Λ (lf D F0) u') (fun F' => BBneP Λ (gS D) (lf D F0) F' P)

def aaS (a : Fin D.R.rS) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))

theorem latSpan_aaS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : latSpan (aaS D) F0.e = XS D F0 := rfl

def IsSplitRow {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  IsSplitBy (aaS D) F0 Λ

def AutFInduces (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Prop :=
  IsRowLat D F0 Λ → IsSplitRow D F0 Λ → autLz D F0 Λ =
    {φ | ∃ β ∈ AutF Λ (lf D F0), ∀ (x : perpS (VS D) F0.X) (hx : β x.1 ∈ perpS (VS D) F0.X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨β x.1, hx⟩}

variable {D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def termBBne (t : Term D u u' F0 what₂) (p : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ F', Rep _ _ _ t.cls F' ∧ BBneF D t.lam (lf D F0) F' p

theorem pd_act (hPD : PDIso D) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (β : AutF Λ (lf D F0))
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} (h : PD D Λ (lf D F0) u' F') :
    PD D Λ (lf D F0) u' (act β F') := by
  have e := hPD u' β.1 (AutF.isom β) Λ (lf D F0) F'
  rw [AutF.lam β, mapL_eq_self β.1 (AutF.isom β) _ (mem_AutF.mp β.2).2.1 (mem_AutF.mp β.2).2.2] at e
  exact e.mpr h

def TSat (TT : Set (Term D u u' F0 what₂)) : Prop :=
  ∀ t ∈ TT, ∀ (β : AutF t.lam (lf D F0)) (x : Carrier (PD D t.lam (lf D F0) u'))
    (h : PD D t.lam (lf D F0) u' (act β x.1)), mk _ _ _ x = t.cls →
      (⟨t.lam, t.mem, mk _ _ _ ⟨act β x.1, h⟩⟩ : Term D u u' F0 what₂) ∈ TT

theorem tsat_of (fam : ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, Set (TermsOf D u' F0 Λ))
    (h : ∀ Λ ∈ what₂, IsSat Λ (lf D F0) (PD D Λ (lf D F0) u') (fam Λ)) :
    TSat (u' := u') (what₂ := what₂) {t | t.cls ∈ fam t.lam} := by
  intro t ht β x hp hx
  exact h t.lam t.mem β x hp (by rw [hx]; exact ht)

theorem sat_BBF (p : HeightOneSpectrum (𝓞 D.host.F)) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hI : BBIso (VS D) D.R.rS (gS D))
    (hF : ∀ P, QFun Λ (lf D F0) (PD D Λ (lf D F0) u') (fun F' => BBneP Λ (gS D) (lf D F0) F' P)) :
    IsSat Λ (lf D F0) (PD D Λ (lf D F0) u') (famOf _ _ _ (fun F' => BBneF D Λ (lf D F0) F' p)) ∧
      IsSat Λ (lf D F0) (PD D Λ (lf D F0) u') (famOf _ _ _ (fun F' => BBneF D Λ (lf D F0) F' p))ᶜ := by
  have hQ : Inv Λ (lf D F0) (fun F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) => BBneF D Λ (lf D F0) F' p) := by
    intro β F'
    simp only [BBneF]
    exact exists_congr (fun P => and_congr_right (fun _ => inv_of_isoInv (hI _ _ P) β F'))
  have hF' : QFun Λ (lf D F0) (PD D Λ (lf D F0) u') (fun F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) => BBneF D Λ (lf D F0) F' p) := by
    intro x y hxy
    simp only [BBneF]
    exact exists_congr (fun P => and_congr_right (fun _ => hF P x y hxy))
  exact ⟨sat_famOf hQ hF', sat_famOf_compl hQ hF'⟩

theorem saturated_term_classes_of_iso (hrows : IsRowReps D F0 what₂) (hTF : TermFun D u u') (hBF : BBFun D u u')
    (hGen : GenIso (VS D) D.R.rS (gS D)) (hRel : RelIso (VS D) D.R.rS D.host.F) (hFeq : FeqFIso (VS D) D.R.rS)
    (hBB : BBIso (VS D) D.R.rS (gS D)) (p : HeightOneSpectrum (𝓞 D.host.F)) :
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.G = 0} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.G ≠ 0} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.generic} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | ¬ t.generic} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.relevant} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | ¬ t.relevant} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.FeqF} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | ¬ t.FeqF} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | termBBne t p} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | ¬ termBBne t p} := by
  have hrow : ∀ Λ ∈ what₂, IsRowLat D F0 Λ := hrows.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tsat_of (fun Λ => {c | Gt _ _ _ c = 0}) (fun Λ hΛ => saturated_g_zero (hTF F0 Λ (hrow Λ hΛ)).1)
  · exact tsat_of (fun Λ => {c | Gt _ _ _ c ≠ 0}) (fun Λ hΛ => sat_Gne (hTF F0 Λ (hrow Λ hΛ)).1)
  · exact tsat_of (fun Λ => {c | IsGen _ _ _ (gS D) c}) (fun Λ hΛ => (sat_gen hGen (hTF F0 Λ (hrow Λ hΛ)).2.2.2.1).1)
  · exact tsat_of (fun Λ => {c | ¬ IsGen _ _ _ (gS D) c}) (fun Λ hΛ => (sat_gen hGen (hTF F0 Λ (hrow Λ hΛ)).2.2.2.1).2)
  · exact tsat_of (fun Λ => {c | IsRel _ _ _ D.host.F c}) (fun Λ hΛ => (sat_rel hRel (hTF F0 Λ (hrow Λ hΛ)).2.2.1).1)
  · exact tsat_of (fun Λ => {c | ¬ IsRel _ _ _ D.host.F c}) (fun Λ hΛ => (sat_rel hRel (hTF F0 Λ (hrow Λ hΛ)).2.2.1).2)
  · exact tsat_of (fun Λ => {c | IsFeqF _ _ _ c}) (fun Λ hΛ => (sat_feqF hFeq (hTF F0 Λ (hrow Λ hΛ)).2.2.2.2).1)
  · exact tsat_of (fun Λ => {c | ¬ IsFeqF _ _ _ c}) (fun Λ hΛ => (sat_feqF hFeq (hTF F0 Λ (hrow Λ hΛ)).2.2.2.2).2)
  · exact tsat_of (fun Λ => famOf _ _ _ (fun F' => BBneF D Λ (lf D F0) F' p))
      (fun Λ hΛ => (sat_BBF p hBB (fun P => hBF F0 Λ (hrow Λ hΛ) P)).1)
  · exact tsat_of (fun Λ => (famOf _ _ _ (fun F' => BBneF D Λ (lf D F0) F' p))ᶜ)
      (fun Λ hΛ => (sat_BBF p hBB (fun P => hBF F0 Λ (hrow Λ hΛ) P)).2)

private theorem rep_iff_lemma_4 {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    {T T' : E} {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {P : LFlag S r T' → Prop}
    {Q : LFlag S r T' → Prop} (hF : QFun Λ F P Q) {t : TermQ Λ F P} {F₁ F₂ : LFlag S r T'}
    (h₁ : Rep Λ F P t F₁) (h₂ : Rep Λ F P t F₂) : Q F₁ ↔ Q F₂ := by
  obtain ⟨p₁, e₁⟩ := h₁
  obtain ⟨p₂, e₂⟩ := h₂
  have k₁ := mem_famOf_mk hF ⟨F₁, p₁⟩
  have k₂ := mem_famOf_mk hF ⟨F₂, p₂⟩
  rw [e₁] at k₁
  rw [e₂] at k₂
  exact k₁.symm.trans k₂

theorem not_bbne_of_generic (hrows : IsRowReps D F0 what₂) (hBF : BBFun D u u')
    {t : Term D u u' F0 what₂} (hg : t.generic) (p : HeightOneSpectrum (𝓞 D.host.F)) : ¬ termBBne t p := by
  rintro ⟨F₂, hrep₂, P, hcomap, hbb⟩
  obtain ⟨F₁, hrep₁, hgen⟩ := hg
  have hQF := hBF F0 t.lam (hrows.1 t.lam t.mem) P
  exact not_BBneP_of_generic hgen P ((rep_iff_lemma_4 hQF hrep₁ hrep₂).mpr hbb)

end D7

end Formalism.L2.SG.Saturated
