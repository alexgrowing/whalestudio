import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TwistLevel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_rfl_apply {a : ℕ} {R : Type} [CommRing R] (x : GL (Fin a) R) : reGL (rfl : a = a) R x = x := by
  ext i j
  rfl

theorem reL_rfl' {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_mem_UPts (σ : E →ₐ[F] E) {a b : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E) (J : Matrix (Fin b) (Fin b) E)
    (hJ : J = G.reindex (finCongr h) (finCongr h)) (R : Type) [CommRing R] [Algebra F R] (x : GL (Fin a) (E ⊗[F] R)) :
    reGL h _ x ∈ UPts σ J R ↔ x ∈ UPts σ G R := by
  subst h
  subst hJ
  rw [reGL_rfl_apply]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]

theorem reGL_mem_levelVL (σ : E →ₐ[F] E) {a b : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E) (J : Matrix (Fin b) (Fin b) E)
    (hJ : J = G.reindex (finCongr h) (finCongr h)) (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin a → E))
    (x : GL (Fin a) (E ⊗[F] v.adicCompletion F)) :
    reGL h _ x ∈ levelVL σ J v (reL h L) ↔ x ∈ levelVL σ G v L := by
  subst h
  subst hJ
  rw [reGL_rfl_apply, reL_rfl']
  simp only [finCongr_refl, Matrix.reindex_refl_refl]

theorem exists_off (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hκ : κ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ Q, bc (prV (E := E) v) y = 1) ∧
      ∀ v, v ∉ Q → bc (prV (E := E) v) y = bc (prV (E := E) v) κ := by
  classical

  have key : ∀ (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v w : HeightOneSpectrum (𝓞 F)), w ≠ v →
      bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 y) = bc (prV (E := E) w) y := by
    intro y v w hw
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe,
      Formalism.UG.P.afsplitC_prV_ne v w hw]
  induction Q using Finset.induction_on with
  | empty => exact ⟨κ, hκ, by simp, fun v _ => rfl⟩
  | @insert v Q hv ih =>
    obtain ⟨y, hy, h1, h2⟩ := ih
    refine ⟨Formalism.UG.P.afsplitU v 1 y, Formalism.UG.P.afsplitU_mem v σ J _ _ (one_mem _) hy, ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · subst hwv
        exact Formalism.UG.P.afsplit_right1 w 1 y
      · rw [key y v w hwv]
        exact h1 w ((Finset.mem_insert.mp hw).resolve_left hwv)
    · intro w hw
      have hwv : w ≠ v := fun e => hw (e ▸ Finset.mem_insert_self v Q)
      rw [key y v w hwv]
      exact h2 w (fun h => hw (Finset.mem_insert_of_mem h))

end Gen

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ}

open Classical in

def ulocQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) :=
  if h : v ∈ Q then W v h else H0.Uloc v

theorem ulocQ_pos (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ Q) :
    ulocQ H0 Q W v = W v h := by
  unfold ulocQ
  exact dif_pos h

theorem ulocQ_neg (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ Q) :
    ulocQ H0 Q W v = H0.Uloc v := by
  unfold ulocQ
  exact dif_neg h

def uQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)) where
  carrier := {x | x ∈ Formalism.L2.Herm.UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ ulocQ H0 Q W v}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun v => by rw [map_mul]; exact mul_mem (hx.2 v) (hy.2 v)⟩
  one_mem' := ⟨one_mem _, fun v => by rw [map_one]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun v => by rw [map_inv]; exact inv_mem (hx.2 v)⟩

def mkLevQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (hWl : ∀ v hv, W v hv ≤ levelVL hc.sig S.gram v H0.Lb)
    (hWQ : ∀ v hv, ∃ N : ℕ, 0 < N ∧ ∀ x, Formalism.L2.Herm.InPrinc hc S v N H0.Lb x → x ∈ W v hv)
    (hQg : ∀ v ∈ Q, ∀ i, (gp i : 𝓞 F) ∉ v.asIdeal) (hQT : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal) :
    Formalism.L2.Herm.StepLevelQ hc S gp T f Q where
  Lb := H0.Lb
  Lb_fin := H0.Lb_fin
  Lb_span := H0.Lb_span
  Lb_int := H0.Lb_int
  Lb_dual := H0.Lb_dual
  Lb_index := H0.Lb_index
  Uloc := ulocQ H0 Q W
  Uloc_lev v := by
    by_cases h : v ∈ Q
    · rw [ulocQ_pos H0 Q W h]; exact hWl v h
    · rw [ulocQ_neg H0 Q W h]; exact H0.Uloc_lev v
  Uloc_hyp v h0 h1 hT hQ := by rw [ulocQ_neg H0 Q W hQ]; exact H0.Uloc_hyp v h0 h1 hT
  Uloc_g i v h x hx := by
    rw [ulocQ_neg H0 Q W (fun hq => hQg v hq i h)]; exact H0.Uloc_g i v h x hx
  UlocAlt v h x := by
    rw [ulocQ_neg H0 Q W (fun hq => hQT v hq h)]; exact H0.UlocAlt v h x
  Uloc_Q v hv := by
    obtain ⟨N, hN, h⟩ := hWQ v hv
    exact ⟨N, hN, fun x hx => by rw [ulocQ_pos H0 Q W hv]; exact h x hx⟩
  U := uQ H0 Q W
  U_eq _ := Iff.rfl

end Lev

end GlobalTheory.Mem.Col2.TwistLevel

end

namespace GlobalTheory.Mem.Col2.TwistLevel

section Abs

def actOfRed {G : Type} [Group G] {ι : Type} {n : ℕ} {k : ι → Type} [∀ i, CommRing (k i)]
    (ρ : G → ∀ i, Matrix (Fin n) (Fin n) (k i)) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b) :
    MulAction G (∀ i, Fin n → k i) where
  smul a y i := ρ a i *ᵥ y i
  one_smul y := by
    funext i
    show ρ 1 i *ᵥ y i = y i
    rw [h1, Pi.one_apply, Matrix.one_mulVec]
  mul_smul a b y := by
    funext i
    show ρ (a * b) i *ᵥ y i = ρ a i *ᵥ (ρ b i *ᵥ y i)
    rw [hm, Pi.mul_apply, Matrix.mulVec_mulVec]

theorem assemble {G : Type} [Group G] {Ch : Type} [Finite Ch] {Qt : Type} [Finite Qt] (Wq : Qt → Type) [∀ q, Group (Wq q)]
    (zQ : G →* ∀ q, Wq q) (Kc : Ch → ∀ q, Subgroup (Wq q)) (hfi : ∀ β q, (Kc β q).FiniteIndex) {V : Type} [Finite V]
    [MulAction G V] (w : Ch → V) (H : Ch → Subgroup G)
    (hH : ∀ β κ, κ ∈ H β ↔ (∀ q, zQ κ q ∈ Kc β q) ∧ κ • w β = w β) :
    ∃ (Yb : Type) (_ : Finite Yb) (_ : MulAction G Yb) (yb : Ch → Yb) (yG : Yb → V) (YQ : Type) (yQ : Yb → YQ),
      (∀ y, ∃! β, ∃ κ : G, κ • yb β = y) ∧ (∀ β (κ : G), κ ∈ H β ↔ κ • yb β = yb β) ∧ (∀ (κ : G) y, yG (κ • y) = κ • yG y) ∧
      (∀ y y', yG y = yG y' → yQ y = yQ y' → y = y') ∧ (∀ (κ : G) y, zQ κ = 1 → yQ (κ • y) = yQ y) := by
  classical
  have hfq : ∀ β q, Finite (Wq q ⧸ Kc β q) := fun β q => by
    haveI := hfi β q
    infer_instance

  let fQ : ∀ β, G ⧸ H β → ∀ q, Wq q ⧸ Kc β q := fun β c =>
    Quotient.liftOn' c (fun g q => ((zQ g q : Wq q) : Wq q ⧸ Kc β q)) (by
      intro a b hab
      have hm := ((hH β (a⁻¹ * b)).mp (QuotientGroup.leftRel_apply.mp hab)).1
      funext q
      apply QuotientGroup.eq.mpr
      simpa [map_mul, map_inv] using hm q)

  let fG : ∀ β, G ⧸ H β → V := fun β c =>
    Quotient.liftOn' c (fun g => g • w β) (by
      intro a b hab
      have hs := ((hH β (a⁻¹ * b)).mp (QuotientGroup.leftRel_apply.mp hab)).2
      rw [mul_smul, inv_smul_eq_iff] at hs
      exact hs.symm)
  have hinj : ∀ (y y' : Σ β, G ⧸ H β), fG y.1 y.2 = fG y'.1 y'.2 →
      (⟨y.1, fQ y.1 y.2⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q) = ⟨y'.1, fQ y'.1 y'.2⟩ → y = y' := by
    rintro ⟨β, c⟩ ⟨β', c'⟩ hG hQ
    obtain rfl : β = β' := congrArg Sigma.fst hQ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective c'
    have hQ' : fQ β g = fQ β g' := eq_of_heq (Sigma.mk.inj hQ).2
    have hG' : g • w β = g' • w β := hG
    have hmem : g⁻¹ * g' ∈ H β := by
      refine (hH β _).mpr ⟨fun q => ?_, ?_⟩
      · have hq : ((zQ g q : Wq q) : Wq q ⧸ Kc β q) = ((zQ g' q : Wq q) : Wq q ⧸ Kc β q) := congrFun hQ' q
        have := QuotientGroup.eq.mp hq
        simpa [map_mul, map_inv] using this
      · rw [mul_smul, ← hG', inv_smul_smul]
    exact congrArg (Sigma.mk β) (QuotientGroup.eq.mpr hmem)
  refine ⟨Σ β, G ⧸ H β,
    Finite.of_injective (fun y => (fG y.1 y.2, (⟨y.1, fQ y.1 y.2⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q)))
      (fun y y' h => hinj y y' (congrArg Prod.fst h) (congrArg Prod.snd h)),
    inferInstance, fun β => ⟨β, ((1 : G) : G ⧸ H β)⟩, fun y => fG y.1 y.2,
    Σ β, ∀ q, Wq q ⧸ Kc β q, fun y => ⟨y.1, fQ y.1 y.2⟩, ?_, ?_, ?_, hinj, ?_⟩
  · rintro ⟨β, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨β, ⟨g, ?_⟩, ?_⟩
    · show (⟨β, g • ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (g : G ⧸ H β)⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    · rintro β' ⟨κ, hκ⟩
      exact congrArg Sigma.fst hκ
  · intro β κ
    have e : κ • (⟨β, ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (κ : G ⧸ H β)⟩ := by
      show (⟨β, κ • ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (κ : G ⧸ H β)⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    show κ ∈ H β ↔ κ • (⟨β, ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, ((1 : G) : G ⧸ H β)⟩
    rw [e]
    constructor
    · intro hk
      exact congrArg (Sigma.mk β) (QuotientGroup.eq.mpr (by simpa using hk))
    · intro hk
      have h2 : (κ : G ⧸ H β) = ((1 : G) : G ⧸ H β) := eq_of_heq (Sigma.mk.inj hk).2
      simpa using QuotientGroup.eq.mp h2
  · rintro κ ⟨β, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show fG β (κ • (g : G ⧸ H β)) = κ • fG β g
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    exact mul_smul κ g (w β)
  · rintro κ ⟨β, c⟩ hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show (⟨β, fQ β (κ • (g : G ⧸ H β))⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q) = ⟨β, fQ β g⟩
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    refine congrArg (Sigma.mk β) (funext fun q => ?_)
    show ((zQ (κ * g) q : Wq q) : Wq q ⧸ Kc β q) = ((zQ g q : Wq q) : Wq q ⧸ Kc β q)
    rw [map_mul, hk, one_mul]

end Abs

end GlobalTheory.Mem.Col2.TwistLevel
