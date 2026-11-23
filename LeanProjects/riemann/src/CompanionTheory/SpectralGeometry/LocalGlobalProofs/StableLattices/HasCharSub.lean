import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ConjQdet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFiniteIdem

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

variable {n : ℕ}

def actML {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M where
  toFun := actM E
  map_add' X Y := by simp only [actM, Matrix.add_apply, add_smul, sum_add_distrib]
  map_smul' c X := by simp only [actM, Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_sum]

theorem actM_single {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b 1) = E a b := by
  classical
  simp [actM, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_smul]

theorem glRel_Eb (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) : GlRel (Eb X B) := by
  have h := GlobalTheory.CapelliLowest.glRel_conj n (actML X.E) ⟨B.U, B.Ui, B.hU, B.hUi⟩ (by
    have : (fun i j => actML X.E (Matrix.single i j 1)) = X.E := by
      funext i j; exact actM_single X.E i j
    rw [this]; exact X.gl)
  exact h

def ebMod (X : GMod n) {A : Matrix (Fin n) (Fin n) ℂ} (B : GradBasis A) : GMod n := ⟨X.V, Eb X B, glRel_Eb X B⟩

def trMod (Y : GMod n) : GMod n where
  V := Module.Dual ℂ Y.V
  E := fun a b => (Y.E b a).dualMap
  gl := fun a b c d => by
    refine LinearMap.ext fun φ => LinearMap.ext fun x => ?_
    have h := comm_apply Y d c b a x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.dualMap_apply, h, map_add, map_sub]
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp; ring
    · subst h1; simp [h2, Ne.symm h2]
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

def quoMod (Y : GMod n) (S : Submodule ℂ Y.V) (h : ∀ a b, ∀ x ∈ S, Y.E a b x ∈ S) : GMod n where
  V := Y.V ⧸ S
  E := fun a b => S.mapQ S (Y.E a b) (fun x hx => h a b x hx)
  gl := fun a b c d => by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective S q
    have h' := comm_apply Y a b c d x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, h']
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub] <;> abel

def bops (Q : GMod n) {c : ℕ} (d : Fin c → ℕ) (h : ∑ i, d i = n) (i : Fin c) : Fin (d i) → Fin (d i) → Module.End ℂ Q.V :=
  fun p q => Q.E (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩)

def Qd (Q : GMod n) {c : ℕ} (d : Fin c → ℕ) (h : ∑ i, d i = n) (i : Fin c) (Y : ℂ) : Module.End ℂ Q.V :=
  qdet (bops Q d h i) (Y + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2)

def leviSub (P : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (χ : Fin n → ℂ) (L : Fin n → Fin 3) : Submodule ℂ P.V where
  carrier := {x | (∀ a b, blk (stdBlocks d h) b < blk (stdBlocks d h) a → P.E a b x = 0) ∧
    ∀ i Y, Qd P d h i Y x = plab χ L i Y • x}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨fun a b hab => by rw [map_add, hx a b hab, hy a b hab, add_zero],
      fun i Y => by rw [map_add, hx', hy', smul_add]⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    exact ⟨fun a b hab => by rw [map_smul, hx a b hab, smul_zero],
      fun i Y => by rw [map_smul, hx', smul_comm]⟩

theorem ofFn_lin {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (f : V →ₗ[ℂ] V') :
    ∀ {t : ℕ} (g : Fin t → Module.End ℂ V) (g' : Fin t → Module.End ℂ V'), (∀ k x, f (g k x) = g' k (f x)) → ∀ x,
      f ((List.ofFn g).prod x) = (List.ofFn g').prod (f x)
  | 0, _, _, _, x => by simp
  | t + 1, g, g', h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, h,
      ofFn_lin f (fun k => g k.succ) (fun k => g' k.succ) (fun k x => h k.succ x)]

theorem qdet_lin {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (f : V →ₗ[ℂ] V') {m : ℕ}
    (E : Fin m → Fin m → Module.End ℂ V) (E' : Fin m → Fin m → Module.End ℂ V')
    (h : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) : f (qdet E u x) = qdet E' u (f x) := by
  have hT : ∀ (v : ℂ) (a b : Fin m) (y : V), f (Tm E v a b y) = Tm E' v a b (f y) := by
    intro v a b y
    unfold Tm
    by_cases hab : a = b <;> simp [hab, h]
  unfold qdet qminor
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul]
  rw [ofFn_lin f _ _ (fun k y => hT _ _ _ y)]

theorem pow_lin {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (f : V →ₗ[ℂ] V')
    (T : Module.End ℂ V) (T' : Module.End ℂ V') (h : ∀ x, f (T x) = T' (f x)) (k : ℕ) (x : V) :
    f ((T ^ k) x) = (T' ^ k) (f x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem shift_lin {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (f : V →ₗ[ℂ] V')
    (T : Module.End ℂ V) (T' : Module.End ℂ V') (h : ∀ x, f (T x) = T' (f x)) (c : ℂ) (x : V) :
    f ((T - c • (1 : Module.End ℂ V)) x) = (T' - c • (1 : Module.End ℂ V')) (f x) := by
  simp [h]

theorem hasChar_sub (Y : GMod n) (S : Submodule ℂ Y.V) (h : ∀ a b, ∀ x ∈ S, Y.E a b x ∈ S) {χ : Fin n → ℂ}
    (hY : HasChar Y χ) : HasChar (Y.sub S h) χ := by
  obtain ⟨k, hk⟩ := hY
  refine ⟨k, fun c => LinearMap.ext fun x => ?_⟩
  have e := pow_lin (V := S) S.subtype _ _
    (shift_lin (V := S) S.subtype (qdet (Y.sub S h).E (c + ((n : ℂ) - 1) / 2)) (qdet Y.E (c + ((n : ℂ) - 1) / 2))
      (fun y => qdet_lin (V := S) S.subtype (Y.sub S h).E Y.E (fun a b x => rfl) _ y) (Formalism.QuantumDeterminants.capP χ c)) k x
  rw [hk c] at e
  exact S.injective_subtype (e.trans (by simp; rfl))

theorem hasChar_quo (Y : GMod n) (S : Submodule ℂ Y.V) (h : ∀ a b, ∀ x ∈ S, Y.E a b x ∈ S) {χ : Fin n → ℂ}
    (hY : HasChar Y χ) : HasChar (quoMod Y S h) χ := by
  obtain ⟨k, hk⟩ := hY
  refine ⟨k, fun c => LinearMap.ext fun q => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective S q
  have e := pow_lin (V' := Y.V ⧸ S) S.mkQ _ _
    (shift_lin (V' := Y.V ⧸ S) S.mkQ (qdet Y.E (c + ((n : ℂ) - 1) / 2)) (qdet (quoMod Y S h).E (c + ((n : ℂ) - 1) / 2))
      (fun y => qdet_lin (V' := Y.V ⧸ S) S.mkQ Y.E (quoMod Y S h).E (fun a b x => rfl) _ y) (Formalism.QuantumDeterminants.capP χ c)) k x
  rw [hk c] at e
  exact e.symm.trans (by simp; rfl)

end GlobalTheory.CompanionTheory.RgTransport
