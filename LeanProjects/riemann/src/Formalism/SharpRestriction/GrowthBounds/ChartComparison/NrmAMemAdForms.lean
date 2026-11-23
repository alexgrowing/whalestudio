import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau]

structure DetTw (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (c : ℤ) where
  ch : UPts σ J (FiniteAdeleRing (𝓞 F) F) →* ℂˣ

  ch_rat : ∀ (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F),
    x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ →
    (ch x : ℂ) * ∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c = 1

  ch_U : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), x.1 ∈ S.U → ch x = 1

def detF {G : Tau → Matrix (Fin n) (Fin n) ℂ} (c : ℤ) (z : Frames G) : ℂ := ∏ τ, (z.1 τ).det ^ c

theorem detF_ne {G : Tau → Matrix (Fin n) (Fin n) ℂ} (c : ℤ) (z : Frames G) : detF c z ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (z.2 τ).ne_zero

def scaleE {α β : Type} (a : α → β → ℂ) (ha : ∀ x z, a x z ≠ 0) : (α → β → ℂ) ≃ₗ[ℂ] (α → β → ℂ) where
  toFun g := fun x z => a x z * g x z
  invFun g := fun x z => (a x z)⁻¹ * g x z
  map_add' g g' := by funext x z; simp [mul_add]
  map_smul' r g := by funext x z; simp; ring
  left_inv g := by funext x z; simp [ha x z]
  right_inv g := by funext x z; simp [ha x z]

@[simp] theorem scaleE_apply {α β : Type} (a : α → β → ℂ) (ha : ∀ x z, a x z ≠ 0) (g : α → β → ℂ) (x : α) (z : β) :
    scaleE a ha g x z = a x z * g x z := rfl

variable {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {c : ℤ}

def DetTw.fac (X : DetTw S emb c) (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (z : Frames (gramC J emb)) : ℂ :=
  (X.ch x : ℂ) * detF c z

theorem DetTw.fac_ne (X : DetTw S emb c) (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (z : Frames (gramC J emb)) :
    X.fac x z ≠ 0 := mul_ne_zero (Units.ne_zero _) (detF_ne c z)

def nrmA (X : DetTw S emb c) :
    (UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ) ≃ₗ[ℂ]
      (UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ) :=
  scaleE X.fac X.fac_ne

def nrm (X : DetTw S emb c) {cls : Type} (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    (cls → Frames (gramC J emb) → ℂ) ≃ₗ[ℂ] (cls → Frames (gramC J emb) → ℂ) :=
  scaleE (fun cl z => X.fac (yc cl) z) (fun cl z => X.fac_ne (yc cl) z)

theorem nrmA_apply (X : DetTw S emb c) (g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ)
    (x : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (z : Frames (gramC J emb)) :
    nrmA X g x z = (X.ch x : ℂ) * detF c z * g x z := rfl

theorem nrm_apply (X : DetTw S emb c) {cls : Type} (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (φ : cls → Frames (gramC J emb) → ℂ) (cl : cls) (z : Frames (gramC J emb)) :
    nrm X yc φ cl z = (X.ch (yc cl) : ℂ) * detF c z * φ cl z := rfl

theorem res_nrmA (X : DetTw S emb c) {cls : Type} (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ) :
    res emb yc (nrmA X g) = nrm X yc (res emb yc g) := rfl

theorem detF_tr (γ : GL (Fin n) E) (y y' : Frames (gramC J emb)) (h : IsTr (atInf emb γ) y' y) :
    detF c y = (∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c) * detF c y' := by
  unfold detF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [h τ, Matrix.det_mul, mul_zpow]
  congr 2
  exact (RingHom.map_det (emb τ) _).symm

theorem DetTw.fac_eq (X : DetTw S emb c) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1)
    (y y' : Frames (gramC J emb)) (hy : IsTr (atInf emb γ) y' y) : X.fac x' y = X.fac x y' := by
  have hγU : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    Formalism.UG.P.rational_points_le_holds F E (Fin n) σ J (FiniteAdeleRing (𝓞 F) F) ⟨γ, hγ, rfl⟩
  have hκU : κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := ((S.U_eq κ.1).1 κ.2).1
  have e : x' = ⟨_, hγU⟩ * x * ⟨_, hκU⟩ := Subtype.ext hx
  have h1 := X.ch_rat γ hγ ⟨_, hγU⟩ rfl
  unfold DetTw.fac
  rw [e, map_mul, map_mul, X.ch_U ⟨_, hκU⟩ κ.2, mul_one, detF_tr γ y y' hy, Units.val_mul]
  calc _ = ((X.ch ⟨_, hγU⟩ : ℂ) * ∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c) * ((X.ch x : ℂ) * detF c y') := by ring
    _ = _ := by rw [h1, one_mul]

theorem nrmA_mem_AdFun (X : DetTw S emb c) (g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ) :
    nrmA X g ∈ AdFun S emb ↔ g ∈ AdFun S emb := by
  constructor
  · intro h γ hγ x x' κ hx y y' hy
    have h1 : X.fac x' y * g x' y = (S.chi κ : ℂ) * (X.fac x y' * g x y') := h γ hγ x x' κ hx y y' hy
    rw [X.fac_eq γ hγ x x' κ hx y y' hy] at h1
    apply mul_left_cancel₀ (X.fac_ne x y')
    rw [h1]; ring
  · intro h γ hγ x x' κ hx y y' hy
    show X.fac x' y * g x' y = (S.chi κ : ℂ) * (X.fac x y' * g x y')
    rw [X.fac_eq γ hγ x x' κ hx y y' hy, h γ hγ x x' κ hx y y' hy]; ring

theorem detF_fnOf (G : Tau → Matrix (Fin n) (Fin n) ℂ) (s : Tau → ℤ) (M : Tau → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, IsUnit (M τ).det) (c : ℤ) (P : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Frames G) :
    detF c z * fnOf G s M P z = (∏ τ, (M τ).det ^ (-c)) * fnOf G (fun τ => s τ + c) M P z := by
  show detF c z * ((∏ τ, (M τ * z.1 τ).det ^ s τ) * _) = (∏ τ, _) * ((∏ τ, (M τ * z.1 τ).det ^ (s τ + c)) * _)
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  unfold detF
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := (hM τ).ne_zero
  have h2 := (z.2 τ).ne_zero
  rw [Matrix.det_mul, zpow_add₀ (mul_ne_zero h1 h2), mul_zpow _ _ c, _root_.zpow_neg]
  have h3 : (M τ).det ^ c ≠ 0 := zpow_ne_zero _ h1
  generalize (M τ).det ^ c = a at h3 ⊢
  generalize (z.1 τ).det ^ c = b
  generalize ((M τ).det * (z.1 τ).det) ^ s τ = d
  have : a⁻¹ * (d * (a * b)) = (a⁻¹ * a) * (b * d) := by ring
  rw [this, inv_mul_cancel₀ h3, one_mul]

theorem shiftOf_shW (hn : 0 < n) (lam : Tau → DomWeight n) (c : ℤ) :
    (fun τ => shiftOf (fun τ => shW (lam τ) c) τ + c) = shiftOf lam := by
  funext τ
  show (shW (lam τ) c).detShift + c = (lam τ).detShift
  rw [detShift_shW _ _ hn]; ring

theorem detF_fnOf_shW (hn : 0 < n) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det)
    (P : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Frames G) :
    detF c z * fnOf G (shiftOf (fun τ => shW (lam τ) c)) M P z = (∏ τ, (M τ).det ^ (-c)) * fnOf G (shiftOf lam) M P z := by
  rw [detF_fnOf G _ M hM c P z, shiftOf_shW hn lam c]

theorem detF_fnOf_one (hn : 0 < n) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ)
    (P : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Frames G) :
    detF c z * fnOf G (shiftOf (fun τ => shW (lam τ) c)) 1 P z = fnOf G (shiftOf lam) 1 P z := by
  rw [detF_fnOf_shW hn G lam c 1 (fun τ => by simp) P z]
  simp

theorem mem_ValC_shW (hn : 0 < n) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ) (a : ℂ) (ha : a ≠ 0)
    (h : Frames G → ℂ) :
    h ∈ ValC G (fun τ => shW (lam τ) c) ↔ (fun z => a * detF c z * h z) ∈ ValC G lam := by
  unfold ValC
  rw [CSpan_shW lam (fun _ => c)]
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨a • P, Submodule.smul_mem _ a hP, ?_⟩
    funext z
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, detF_fnOf_one hn]
  · rintro ⟨P, hP, hPh⟩
    refine ⟨a⁻¹ • P, Submodule.smul_mem _ _ hP, ?_⟩
    funext z
    have h1 : fnOf G (shiftOf lam) 1 P z = a * detF c z * h z := congrFun hPh z
    rw [← detF_fnOf_one hn G lam c P z] at h1
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    have h2 : detF c z * fnOf G (shiftOf (fun τ => shW (lam τ) c)) 1 P z = detF c z * (a * h z) := by rw [h1]; ring
    rw [mul_left_cancel₀ (detF_ne c z) h2, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem nrmA_mem_AdForms (hn : 0 < n) (X : DetTw S emb c) (lam : Tau → DomWeight n)
    (g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ) :
    nrmA X g ∈ AdForms S emb lam ↔ g ∈ AdForms S emb (fun τ => shW (lam τ) c) := by
  unfold AdForms
  rw [Submodule.mem_inf, Submodule.mem_inf, nrmA_mem_AdFun, Submodule.mem_pi, Submodule.mem_pi]
  refine and_congr Iff.rfl (forall_congr' fun x => forall_congr' fun _ => ?_)
  exact (mem_ValC_shW hn (gramC J emb) lam c (X.ch x : ℂ) (Units.ne_zero _) (g x)).symm

theorem FiC_nrm (hn : 0 < n) (X : DetTw S emb c) (lam : Tau → DomWeight n) {cls : Type}
    (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (φ : cls → Frames (gramC J emb) → ℂ) :
    nrm X yc φ ∈ FiC S emb lam yc ↔ φ ∈ FiC S emb (fun τ => shW (lam τ) c) yc := by
  unfold FiC
  constructor
  · rintro ⟨g', hg', h⟩
    refine ⟨(nrmA X).symm g', (nrmA_mem_AdForms hn X lam _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hg'), ?_⟩
    apply (nrm X yc).injective
    rw [← res_nrmA, LinearEquiv.apply_symm_apply]
    exact h
  · rintro ⟨g, hg, rfl⟩
    exact ⟨nrmA X g, (nrmA_mem_AdForms hn X lam g).2 hg, res_nrmA X yc g⟩

theorem nrm_val_one (hn : 0 < n) (a : ℂ) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ)
    (Q : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Frames G) (v : ℂ)
    (hv : v = fnOf G (shiftOf (fun τ => shW (lam τ) c)) 1 Q z) :
    a * detF c z * v = a * fnOf G (shiftOf lam) 1 Q z := by
  rw [hv, mul_assoc, detF_fnOf_one hn]

theorem nrm_val_M (hn : 0 < n) (a : ℂ) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det)
    (Q : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Frames G) (v : ℂ)
    (hv : v = fnOf G (shiftOf (fun τ => shW (lam τ) c)) M Q z) :
    a * detF c z * v = a * ((∏ τ, (M τ).det ^ (-c)) * fnOf G (shiftOf lam) M Q z) := by
  rw [hv, mul_assoc, detF_fnOf_shW hn G lam c M hM]

theorem nrm_val_M' (hn : 0 < n) (a : ℂ) (ha : a ≠ 0) (G : Tau → Matrix (Fin n) (Fin n) ℂ) (lam : Tau → DomWeight n) (c : ℤ)
    (M : Tau → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det)
    (Q : MvPolynomial (Tau × Fin n × Fin n) ℂ) (z : Frames G) (v : ℂ)
    (hv : a * detF c z * v = a * ((∏ τ, (M τ).det ^ (-c)) * fnOf G (shiftOf lam) M Q z)) :
    v = fnOf G (shiftOf (fun τ => shW (lam τ) c)) M Q z := by
  rw [mul_assoc, ← detF_fnOf_shW hn G lam c M hM] at hv
  exact mul_left_cancel₀ (detF_ne _ _) (mul_left_cancel₀ ha hv)

end Gen

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def cTw (D : D7) (i : ℕ) : ℤ := ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)

theorem cTw_zero (D : D7) : cTw D 0 = 0 := by simp [cTw]

theorem lamTG_eq (i : ℕ) : lamTG M i = fun τ => shW (M.lam i τ) (cTw D i) := rfl

theorem atInf_det_unit {E : Type} [Field E] {Tau : Type} {n : ℕ} (emb : Tau → E →+* ℂ) (B : GL (Fin n) E) (τ : Tau) :
    IsUnit (atInf emb (B : Matrix (Fin n) (Fin n) E) τ).det := by
  have h : (atInf emb (B : Matrix (Fin n) (Fin n) E) τ).det = emb τ (B : Matrix (Fin n) (Fin n) E).det :=
    (RingHom.map_det (emb τ) _).symm
  rw [h]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).map (emb τ)

variable {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi)
  {okW : D.what₂.places.Pl → Prop} {Ch : Type} (chOf : C.cls i → Ch)
  {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
  (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1))

def embCh (β : Ch) : (M.lat i).V →ₛₗ[D.what₂.embLL] ({c // chOf c = β} → Fr D i hi → ℂ) where
  toFun x := fun cl z => M.emb i x cl.1 (eY.symm z)
  map_add' x y := by funext cl z; rw [map_add]; rfl
  map_smul' a x := by funext cl z; rw [LinearMap.map_smulₛₗ]; rfl

def embN (β : Ch) (X : DetTw (K β).lev (embT D) (cTw D i)) :
    (M.lat i).V →ₛₗ[D.what₂.embLL] ({c // chOf c = β} → Fr D i hi → ℂ) :=
  ((nrm X (K β).y).toLinearMap).comp (embCh M eY chOf β)

theorem embN_apply (β : Ch) (X : DetTw (K β).lev (embT D) (cTw D i)) (x : (M.lat i).V) (cl : {c // chOf c = β})
    (z : Fr D i hi) :
    embN M eY chOf K β X x cl z = (X.ch ((K β).y cl) : ℂ) * detF (cTw D i) z * M.emb i x cl.1 (eY.symm z) := rfl

theorem embN_inj (X : ∀ β, DetTw (K β).lev (embT D) (cTw D i)) (x y : (M.lat i).V)
    (h : ∀ β, embN M eY chOf K β (X β) x = embN M eY chOf K β (X β) y) : x = y := by
  apply M.emb_inj i
  funext c z
  have h1 := congrFun (congrFun (h (chOf c)) ⟨c, rfl⟩) (eY z)
  rw [embN_apply, embN_apply, Equiv.symm_apply_apply] at h1
  exact mul_left_cancel₀ ((X (chOf c)).fac_ne _ _) h1

variable {M eY chOf K}

theorem embN_mem_FiC (V : ValuationCompatibleChart M eY okW chOf K) (β : Ch) (X : DetTw (K β).lev (embT D) (cTw D i)) (x : (M.lat i).V) :
    embN M eY chOf K β X x ∈ FiC (K β).lev (embT D) (M.lam i) (K β).y :=
  (FiC_nrm (D.R.N_pos i) X (M.lam i) (K β).y _).2 ((V.Fi _).1 ((V.rat _).1 ⟨x, rfl⟩).1 β)

set_option maxHeartbeats 1000000 in

theorem embN_rat (V : ValuationCompatibleChart M eY okW chOf K) (β : Ch) (X : DetTw (K β).lev (embT D) (cTw D i)) (x : (M.lat i).V)
    (cl : {c // chOf c = β}) : ∃ Q ∈ RatSpan D (M.lam i), ∀ z : Fr D i hi,
      embN M eY chOf K β X x cl z =
        (X.ch ((K β).y cl) : ℂ) * fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (M.lam i)) 1 Q z := by
  obtain ⟨Q, hQ, hz⟩ := ((V.rat _).1 ⟨x, rfl⟩).2 cl.1
  refine ⟨Q, hQ, fun z => ?_⟩
  exact (embN_apply M eY chOf K β X x cl z).trans
    (nrm_val_one (D.R.N_pos i) _ (gramC (gramN D i hi) (embT D)) (M.lam i) (cTw D i) Q z _
      ((hz (eY.symm z)).trans (congrArg _ (eY.apply_symm_apply z))))

set_option maxHeartbeats 2000000 in

theorem embN_lat (V : ValuationCompatibleChart M eY okW chOf K) (X : ∀ β, DetTw (K β).lev (embT D) (cTw D i)) (w : D.what₂.places.Pl)
    (hw : okW w) (x : (M.lat i).V) :
    x ∈ M.S i w ↔ ∀ (β : Ch) (cl : {c // chOf c = β}) (B : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (lat cl.1)) B →
      ∃ Q ∈ IntSpan D w (M.lam i), ∀ z : Fr D i hi,
        embN M eY chOf K β (X β) x cl z =
          ((X β).ch ((K β).y cl) : ℂ) *
            ((∏ τ, (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ).det ^ (-(cTw D i))) *
              fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (M.lam i))
                (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q z) := by
  rw [V.lat w hw x]
  constructor
  · intro h β cl B hB
    obtain ⟨Q, hQ, hz⟩ := h cl.1 B hB
    refine ⟨Q, hQ, fun z => ?_⟩
    exact (embN_apply M eY chOf K β (X β) x cl z).trans
      (nrm_val_M (D.R.N_pos i) _ (gramC (gramN D i hi) (embT D)) (M.lam i) (cTw D i) _ (atInf_det_unit (embT D) B⁻¹) Q z _
        ((hz (eY.symm z)).trans (congrArg _ (eY.apply_symm_apply z))))
  · intro h c B hB
    obtain ⟨Q, hQ, hz⟩ := h (chOf c) ⟨c, rfl⟩ B hB
    refine ⟨Q, hQ, fun z => ?_⟩
    have h1 := (embN_apply M eY chOf K (chOf c) (X (chOf c)) x ⟨c, rfl⟩ (eY z)).symm.trans (hz (eY z))
    have h2 := nrm_val_M' (D.R.N_pos i) _ (Units.ne_zero _) (gramC (gramN D i hi) (embT D)) (M.lam i) (cTw D i) _
      (atInf_det_unit (embT D) B⁻¹) Q (eY z) _ h1
    exact (congrArg (M.emb i x c) (eY.symm_apply_apply z)).symm.trans h2

end Rec

section ChiD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m}

structure DetTie (S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) where
  dt : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →* D.Dt
  dt_rat : ∀ (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    ∀ x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ →
    ∃ z : unitary D.host.E, (z : D.host.E) = (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).det ∧ dt x = D.e1Dt z
  dt_U : ∀ x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1 ∈ S.U → dt x ∈ D.UO

def DetTw.ofChiD {S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad} (Y : DetTie S) (c : ℤ) :
    DetTw S (embT D) c where
  ch := (zpowGroupHom c).comp (D.chiD.comp Y.dt)
  ch_rat := by
    intro γ hγ x hx
    obtain ⟨z, hz, hd⟩ := Y.dt_rat γ hγ x hx
    show (((D.chiD (Y.dt x)) ^ c : ℂˣ) : ℂ) * _ = 1
    rw [hd, Units.val_zpow_eq_zpow_val, D.rest_detCharacter_on_unitary_eq z, ← hz, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    have hne : embT D τ (z : D.host.E) ≠ 0 := by
      have hu : IsUnit (z : D.host.E) := (Unitary.toUnits z).isUnit
      exact (hu.map (embT D τ)).ne_zero
    show ((embT D τ (z : D.host.E))⁻¹) ^ c * (embT D τ (z : D.host.E)) ^ c = 1
    rw [_root_.inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ hne)]
  ch_U := by
    intro x hx
    show (D.chiD (Y.dt x)) ^ c = 1
    rw [D.chiD_UO _ (Y.dt_U x hx), _root_.one_zpow]

end ChiD

end Formalism.MainNotions.G.CmpJ

end
