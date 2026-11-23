import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermCompatId

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section Kos
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
  {κ : Type} [LinearOrder κ]

def KE {M : Type} [AddCommGroup M] [Module ℂ M] (C : Cx ℂ M) (d : ℤ) : Prop := ∀ m < d, C.Z m ≤ C.B m

def sm (M : Submodule ℂ E) (T : Set S) : Submodule ℂ E := ⨆ r ∈ T, M.map (act r)

def Stab (R : Subalgebra ℂ S) (M : Submodule ℂ E) : Prop := ∀ r ∈ R, ∀ m ∈ M, act r m ∈ M

def Reg (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) : Prop :=
  ∀ k : Fin d, ∀ m ∈ M, act (f k) m ∈ sm act M (f '' {j | j < k}) → m ∈ sm act M (f '' {j | j < k})

def kos (M : Submodule ℂ E) (r : κ → S) : Cx ℂ (Finset κ → E) := acx (fun _ => M) fun l => act (r l)

def kosT (M : Submodule ℂ E) (u : κ → Sˣ) (z : κ → S) : Cx ℂ (Finset κ → E) :=
  acx (fun L => M.map (act ((∏ l ∈ L, u l : Sˣ) : S))) fun l => act (z l)

def unsc (u : κ → Sˣ) (c : Finset κ → E) : Finset κ → E := fun L => act (((∏ l ∈ L, u l)⁻¹ : Sˣ) : S) (c L)

def detC {p : ℕ} (ρ : κ → Fin p → S) (s : Finset κ) : S :=
  if h : s.card = p then (Matrix.of fun a b => ρ (s.orderEmbOfFin h a) b).det else 0

end Kos

section Idx
variable {β κ κ' E : Type} [LinearOrder β] [LinearOrder κ] [LinearOrder κ']

def col (c : Finset (β ⊕ₗ κ) → E) (b : Finset β) : Finset κ → E := fun L => c (uni b L)

def resK (e : κ' ↪o κ) (c : Finset (β ⊕ₗ κ) → E) : Finset (β ⊕ₗ κ') → E := fun s => c (uni (lft s) ((rgt s).map e.toEmbedding))

def top (c : Finset (β ⊕ₗ κ) → E) : Finset β → E := fun b => c (uni b ∅)

def inlE : β ↪o β ⊕ₗ κ := OrderEmbedding.ofStrictMono _ Sum.Lex.inl_strictMono
def inrE : κ ↪o β ⊕ₗ κ := OrderEmbedding.ofStrictMono _ Sum.Lex.inr_strictMono

def img {d : ℕ} (e : Fin d ↪o κ) : Finset κ := Finset.univ.map e.toEmbedding

def pk {d : ℕ} (I : Finset (Fin (d + 1))) : Fin (d + 1) := if h : I.Nonempty then I.min' h else 0

abbrev Two (d : ℕ) : Type := Fin (d + 1) ⊕ₗ Fin (d + 1)

abbrev Mi (d : ℕ) : Type := Fin (d + 1) ×ₗ Fin (d + 1)

def dj {d : ℕ} (j : Fin (d + 1)) : Fin d ↪o Mi d :=
  OrderEmbedding.ofStrictMono (fun l => toLex (j.succAbove l, j)) fun _ _ h =>
    Prod.Lex.left _ _ (Fin.strictMono_succAbove j h)

end Idx

structure Sys (d : ℕ) (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] where
  act : S →ₐ[ℂ] Module.End ℂ E
  X : Fin (d + 1) → Sˣ
  Y : Fin (d + 1) → Sˣ
  R : Finset (Fin (d + 1)) → Finset (Fin (d + 1)) → Subalgebra ℂ S
  M : Finset (Fin (d + 1)) → Finset (Fin (d + 1)) → Submodule ℂ E

namespace Sys
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  {κ : Type} [LinearOrder κ]

structure Good : Prop where
  monoR : ∀ I I' J J', I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' → T.R I J ≤ T.R I' J'
  monoM : ∀ I I' J J', I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' → T.M I J ≤ T.M I' J'
  stab : ∀ I J, I.Nonempty → J.Nonempty → Stab T.act (T.R I J) (T.M I J)
  memX : ∀ I J, J.Nonempty → ∀ i ∈ I, ∀ a, ((T.X a * (T.X i)⁻¹ : Sˣ) : S) ∈ T.R I J
  memY : ∀ I J, I.Nonempty → ∀ j ∈ J, ∀ a, ((T.Y a * (T.Y j)⁻¹ : Sˣ) : S) ∈ T.R I J

def u (n : κ → ℕ × ℕ) (i j : Fin (d + 1)) (l : κ) : Sˣ := T.X i ^ (n l).1 * T.Y j ^ (n l).2

def r (n : κ → ℕ × ℕ) (z : κ → S) (i j : Fin (d + 1)) (l : κ) : S := z l * ((T.u n i j l)⁻¹ : Sˣ)

def admitted (n : κ → ℕ × ℕ) (z : κ → S) : Prop := ∀ i j l, T.r n z i j l ∈ T.R {i} {j}

def colCx (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) : Cx ℂ (Finset κ → E) :=
  kosT T.act (T.M I J) (T.u n (pk I) (pk J)) z

def wt (z : κ → S) : Two d ⊕ₗ κ → Module.End ℂ E := fun t => Sum.elim (fun _ => 1) (fun l => T.act (z l)) (ofLex t)

def cx (n : κ → ℕ × ℕ) (z : κ → S) : Cx ℂ (Finset (Two d ⊕ₗ κ) → E) :=
  acx (fun s => mixF (fun I J => (T.M I J).map (T.act ((∏ l ∈ rgt s, T.u n (pk I) (pk J) l : Sˣ) : S))) (lft s)) (T.wt z)

def mix : Cx ℂ (Finset (Two d) → E) := acx (mixF T.M) fun _ => 1

def mu (l : Mi d) : S := T.X (ofLex l).1 * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1

def rowMu : Fin (d + 1) ⊕ₗ Mi d → Fin (d + 1) → S := fun t => Sum.elim (fun i => Pi.single i 1)
  (fun l m => (if m = (ofLex l).1 then (T.X m * T.Y (ofLex l).2 : S) else 0) -
    if m = (ofLex l).2 then (T.X m * T.Y (ofLex l).1 : S) else 0) (ofLex t)

def rowT : Fin (d + 1) ⊕ₗ Fin d → Fin (d + 1) → S := fun t => Sum.elim (fun i => Pi.single i 1)
  (fun l => Pi.single l.succ (T.X l.succ : S)) (ofLex t)

def mj (p : ℕ) (θ : Finset (Fin (d + 1) ⊕ₗ κ) → S) (b : Finset (Fin (d + 1)) → E) : Finset (Two d ⊕ₗ κ) → E := fun s =>
  ((-1 : ℤ) ^ ((p + 1) * (rgt s).card)) • T.act (θ (uni (lft (lft s)) (rgt s))) (b (rgt (lft s)))

end Sys

def n11 {κ : Type} : κ → ℕ × ℕ := fun _ => (1, 1)

def app {κ κ' A : Type} (f : κ → A) (g : κ' → A) : κ ⊕ₗ κ' → A := fun t => Sum.elim f g (ofLex t)

def rcup {d : ℕ} {κ E E' E'' : Type} [LinearOrder κ] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup E''] [Module ℂ E''] (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'') (p : ℕ) (c : Finset (Two d ⊕ₗ κ) → E)
    (x : Finset (Fin (d + 1)) → E') : Finset (Two d ⊕ₗ κ) → E'' := fun s =>
  ((-1 : ℤ) ^ (p * ((rgt (lft s)).card + (rgt s).card))) • ∑ i ∈ lft (lft s),
    μ (c (uni (uni ((lft (lft s)).filter (· ≤ i)) (rgt (lft s))) (rgt s))) (x ((lft (lft s)).filter (i ≤ ·)))

section Inst
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

abbrev xv : Fin (d + 1) → F := fun i => x i

def sysZ (a : ℕ) : Sys d (K ⊗[ℂ] K) (DR ℂ K ⊗[ℂ] DR ℂ K) where
  act := actZ K
  X i := Units.map ((Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap F K) : F →+* K ⊗[ℂ] K) : F →* K ⊗[ℂ] K) (x i)
  Y i := Units.map (((Algebra.TensorProduct.includeRight : K →ₐ[ℂ] K ⊗[ℂ] K).toRingHom.comp (algebraMap F K) : F →+* K ⊗[ℂ] K) :
    F →* K ⊗[ℂ] K) (x i)
  R I J := (Algebra.TensorProduct.map (rB ℂ K (xv x) I).val (rB ℂ K (xv x) J).val).range
  M := MZ F K (xv x) a

def sysP (a : ℕ) : Sys d (F ⊗[ℂ] K) (F ⊗[ℂ] DR ℂ K) where
  act := (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ F) (Algebra.lsmul ℂ ℂ (DR ℂ K)))
  X i := Units.map ((Algebra.TensorProduct.includeLeftRingHom : F →+* F ⊗[ℂ] K) : F →* F ⊗[ℂ] K) (x i)
  Y i := Units.map (((Algebra.TensorProduct.includeRight : K →ₐ[ℂ] F ⊗[ℂ] K).toRingHom.comp (algebraMap F K) : F →+* F ⊗[ℂ] K) :
    F →* F ⊗[ℂ] K) (x i)
  R I J := (Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rB ℂ K (xv x) J).val).range
  M I J := Submodule.map₂ (TensorProduct.mk ℂ _ _) (omA ℂ (xv x) I) (omB ℂ K (rB ℂ K (xv x) J) a)

variable (F) in

def muP (τ : DR ℂ K →ₗ[K] K) : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K →ₗ[ℂ] F ⊗[ℂ] DR ℂ K :=
  LinearMap.flip (LinearMap.rTensorHom (DR ℂ K) ∘ₗ (LinearMap.mul ℂ (DR ℂ K)).flip.compr₂
    ((Algebra.trace F K).restrictScalars ℂ ∘ₗ τ.restrictScalars ℂ))

variable (F) in

def mulP : F ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  TensorProduct.lift ((Algebra.lsmul ℂ ℂ (DR ℂ K)).toLinearMap ∘ₗ (Algebra.linearMap F K).restrictScalars ℂ)

def Acts (τ : DR ℂ K →ₗ[K] K) (a : ℕ) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (c : K) : Prop :=
  ∀ w ∈ ⋀[K]^a Ω[K⁄ℂ], mulP F K (muP F K τ m w) = c • w

def kap (L : Finset (Mi d)) : K :=
  Algebra.TensorProduct.lmul' ℂ (detC (sysZ K x 0).rowMu (uni {0} L))

variable {K} {K' : Type} [Field K'] [Algebra ℂ K'] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
  [IsScalarTower ℂ F K']

def sysY (j2 : K →ₐ[ℂ] K') (a : ℕ) : Sys d K' (DR ℂ K') where
  act := Algebra.lsmul ℂ ℂ (DR ℂ K')
  X i := Units.map (algebraMap F K' : F →* K') (x i)
  Y i := Units.map ((j2.toRingHom.comp (algebraMap F K) : F →+* K') : F →* K') (x i)
  R := RY (xv x) j2
  M I J := omB ℂ K' (RY (xv x) j2 I J) a

def RF (j2 : K →ₐ[ℂ] K') (s : Finset (Two d)) : Subalgebra ℂ K' :=
  if (rgt s).Nonempty then (if (lft s).Nonempty then RY (xv x) j2 (lft s) (rgt s) else R2 (xv x) j2 (rgt s))
  else rB ℂ K' (xv x) (lft s)

def gS (j2 : K →ₐ[ℂ] K') : K ⊗[ℂ] K →ₐ[ℂ] K' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ K K') j2

end Inst

section Loc
variable {L : Type} [Field L] [Algebra ℂ L]

def loc (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) : Subalgebra ℂ L where
  carrier := {v | ∃ b : B, e b ≠ 0 ∧ (b : L) * v ∈ B}
  mul_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', by simp [hb, hb'], ?_⟩
    have := B.mul_mem h h'
    rwa [show (b : L) * v * (b' * v') = ((b * b' : B) : L) * (v * v') by push_cast; ring] at this
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', by simp [hb, hb'], ?_⟩
    have := B.add_mem (B.mul_mem b'.2 h) (B.mul_mem b.2 h')
    rwa [show (b' : L) * (b * v) + b * (b' * v') = ((b * b' : B) : L) * (v + v') by push_cast; ring] at this
  algebraMap_mem' c := ⟨1, by simp, by simpa using B.algebraMap_mem c⟩

def van (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) : Set L := {v | Val B e v 0}

variable {F : Type} [Field F] [Algebra ℂ F] [Algebra F L] {d : ℕ} (x : Fin (d + 1) → Fˣ)

variable (L) in

def tt (j : Fin d) : L := algebraMap F L ((x j.succ : F) / x 0)

variable (L) in

def dtS (S : Finset (Fin d)) : DR ℂ L :=
  ExteriorAlgebra.ιMulti L S.card fun a => D ℂ L (tt L x (S.orderEmbOfFin rfl a))

end Loc

end UpperTheory.Gal.productCup_of_system

end
