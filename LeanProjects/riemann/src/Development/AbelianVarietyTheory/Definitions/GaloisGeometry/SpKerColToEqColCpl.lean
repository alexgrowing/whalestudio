import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumFibreEqSumOrbits
import Formalism.LocalToGlobal.KernelLattices.ThDistC

noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure MemOn (F : GFam K) where

  G : Type
  [grpG : Group G]

  D : Type
  [actD : MulAction G D]

  ρ : G →* Module.End K F.V

  Nab : D → Submodule (𝓞 K) F.V

  Del : D → Submodule (𝓞 K) F.V

attribute [instance] MemOn.grpG MemOn.actD

@[reducible] def MemOn.gsd {F : GFam K} (M : MemOn F) : GSD K where
  G := M.G
  D := M.D
  V := F.V
  ιV := F.ιV
  bV := F.bV
  pair := F.pair
  ρ := M.ρ
  Nab := M.Nab
  Del := M.Del

@[reducible] def MemOn.self (F : GFam K) (b : F.β) : MemOn F where
  G := F.G b
  D := F.D b
  ρ := F.ρ b
  Nab := F.Nab b
  Del := F.Del b

@[reducible] def MemOn.pairs (F : GFam K) (b : F.β) (Y : Cpl (F.mem b)) : MemOn F where
  G := F.G b
  D := Y.Pts
  actD := (cplGSD (F.mem b) Y).actD
  ρ := F.ρ b
  Nab d := F.Nab b d.1.1
  Del d := F.Del b d.1.1

example (F : GFam K) (b : F.β) : (MemOn.self F b).gsd = F.mem b := rfl

example (F : GFam K) (b : F.β) (Y : Cpl (F.mem b)) : (MemOn.pairs F b Y).gsd = cplGSD (F.mem b) Y := rfl

inductive SpIdx (β : ℕ → Type) (n m i : ℕ) : Type
  | mat (b : β i) (h : i ≤ n) : SpIdx β n m i
  | cpl (h : i = n + 1) : SpIdx β n m i
  | top (h : i = m) : SpIdx β n m i

namespace SpIdx

variable {β : ℕ → Type} {n m i : ℕ}

instance [Finite (β i)] : Finite (SpIdx β n m i) :=
  Finite.of_injective (fun b : SpIdx β n m i => match b with
    | .mat b _ => (Sum.inl b : β i ⊕ Bool)
    | .cpl _ => Sum.inr false
    | .top _ => Sum.inr true) (by
      rintro (⟨a, _⟩ | _ | _) (⟨b, _⟩ | _ | _) h <;> simp_all)

instance [Finite (β i)] : Fintype (SpIdx β n m i) := Fintype.ofFinite _

instance : DecidableEq (SpIdx β n m i) := Classical.decEq _

def lowEquiv (hm : n < m) (hi : i ≤ n) : β i ≃ SpIdx β n m i where
  toFun b := .mat b hi
  invFun b := match b with
    | .mat b _ => b
    | .cpl h => absurd h (by omega)
    | .top h => absurd h (by omega)
  left_inv _ := rfl
  right_inv b := match b with
    | .mat _ _ => rfl
    | .cpl h => absurd h (by omega)
    | .top h => absurd h (by omega)

theorem eq_cpl (hm : m ≠ n + 1) (h : i = n + 1) (b : SpIdx β n m i) : b = .cpl h := by
  rcases b with ⟨_, h'⟩ | _ | h'
  · omega
  · rfl
  · omega

theorem eq_top (hm : n + 1 < m) (h : i = m) (b : SpIdx β n m i) : b = .top h := by
  rcases b with ⟨_, h'⟩ | h' | _
  · omega
  · omega
  · rfl

theorem isEmpty_of_lt (hm : n + 1 < m) (h : m < i) : IsEmpty (SpIdx β n m i) :=
  ⟨fun b => by rcases b with ⟨_, h'⟩ | h' | h' <;> omega⟩

end SpIdx

section Splice

variable (F : ℕ → GFam K) (n m : ℕ) (C : MemOn (F (n + 1))) (T : MemOn (F m))

@[reducible] def spMem : ∀ (i : ℕ) (_ : SpIdx (fun j => (F j).β) n m i), MemOn (F i)
  | i, .mat b _ => MemOn.self (F i) b
  | _, .cpl rfl => C
  | _, .top rfl => T

@[reducible] def spFam (i : ℕ) : GFam K where
  β := SpIdx (fun j => (F j).β) n m i
  V := (F i).V
  ιV := (F i).ιV
  bV := (F i).bV
  pair := (F i).pair
  G b := (spMem F n m C T i b).G
  D b := (spMem F n m C T i b).D
  ρ b := (spMem F n m C T i b).ρ
  Nab b := (spMem F n m C T i b).Nab
  Del b := (spMem F n m C T i b).Del

theorem spFam_mem_mat (i : ℕ) (b : (F i).β) (h : i ≤ n) : (spFam F n m C T i).mem (.mat b h) = (F i).mem b := rfl

theorem spFam_mem_cpl (h : n + 1 = n + 1) : (spFam F n m C T (n + 1)).mem (.cpl h) = C.gsd := rfl

theorem spFam_mem_top (h : m = m) : (spFam F n m C T m).mem (.top h) = T.gsd := rfl

variable {F n m C T}

theorem spFam_ok (hF : ∀ i, i ≤ n → (F i).Ok) (hC : C.gsd.Ok) (hT : T.gsd.Ok) (i : ℕ) : (spFam F n m C T i).Ok := by
  rintro (⟨b, h⟩ | rfl | rfl)
  · exact hF i h b
  · exact hC
  · exact hT

def spEntry (kk : KerFam F) (k1 : ∀ al : (F n).β, ClsKer ((F n).mem al) C.gsd) (k2 : ClsKer C.gsd T.gsd)
    (i j : ℕ) (e : j = i + 1) : ∀ (b : (spFam F n m C T i).β) (b' : (spFam F n m C T j).β),
      ClsKer ((spFam F n m C T i).mem b) ((spFam F n m C T j).mem b')
  | .mat al _, .mat be _ => (match j, e, be with | _, rfl, be => kk i al be : ClsKer ((F i).mem al) ((F j).mem be))
  | .mat al _, .cpl h' =>
    (match i, j, (Nat.succ.inj (h'.symm.trans e) : n = i), h', al with | _, _, rfl, rfl, al => k1 al :
      ClsKer ((F i).mem al) ((spFam F n m C T j).mem (.cpl h')))
  | .cpl h, .top h' =>
    (match i, j, h, h' with | _, _, rfl, rfl => k2 :
      ClsKer ((spFam F n m C T i).mem (.cpl h)) ((spFam F n m C T j).mem (.top h')))
  | .mat _ _, .top _ => zeroKer _ _
  | .cpl _, .mat _ _ => zeroKer _ _
  | .cpl _, .cpl _ => zeroKer _ _
  | .top _, _ => zeroKer _ _

variable (kk : KerFam F) (k1 : ∀ al : (F n).β, ClsKer ((F n).mem al) C.gsd) (k2 : ClsKer C.gsd T.gsd)

def spKer : KerFam (spFam F n m C T) := fun i b b' => spEntry kk k1 k2 i (i + 1) rfl b b'

theorem spKer_mat (i : ℕ) (al : (F i).β) (be : (F (i + 1)).β) (h : i ≤ n) (h' : i + 1 ≤ n) :
    spKer kk k1 k2 i (.mat al h) (.mat be h') = kk i al be := rfl

theorem spKer_cpl (al : (F n).β) (h : n ≤ n) (h' : n + 1 = n + 1) : spKer kk k1 k2 n (.mat al h) (.cpl h') = k1 al := rfl

theorem spEntry_top (e : m = n + 1 + 1) (h : n + 1 = n + 1) (h' : m = m) : spEntry kk k1 k2 (n + 1) m e (.cpl h) (.top h') = k2 := rfl

variable (n m C T) in

def spIn (i : ℕ) : (F i).Forms →ₗ[K] (spFam F n m C T i).Forms :=
  LinearMap.pi fun b => match b with
    | .mat al _ => LinearMap.proj al
    | .cpl _ => 0
    | .top _ => 0

theorem spIn_mat (i : ℕ) (φ : (F i).Forms) (al : (F i).β) (h : i ≤ n) : spIn n m C T i φ (.mat al h) = φ al := rfl

variable {hS : ∀ i, (spFam F n m C T i).Ok}

theorem spKer_colTo_low (hm : n < m) (hF : ∀ i, (F i).Ok) (φ : (F 0).Forms) (i : ℕ) (hi : i ≤ n) (al : (F i).β) :
    (spKer kk k1 k2).colTo hS i (spIn n m C T 0 φ) (.mat al hi) = kk.colTo hF i φ al := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i ≤ n := by omega
    show (∑ b : (spFam F n m C T i).β, ((spKer kk k1 k2 i b (.mat al hi)).opOf (hS i b) _) ∘ₗ (LinearMap.proj b)) _ =
      (∑ b : (F i).β, ((kk i b al).opOf (hF i b) _) ∘ₗ (LinearMap.proj b)) _
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    refine (Fintype.sum_equiv (SpIdx.lowEquiv (β := fun j => (F j).β) hm hi') _ _ fun b => ?_).symm
    exact congrArg ((kk i b al).opOf (hF i b) ((F i).mem b).outSec) (ih hi' b).symm

theorem spKer_colTo_cpl (hm : n < m) (hF : ∀ i, (F i).Ok) (φ : (F 0).Forms) (h : n + 1 = n + 1) :
    (spKer kk k1 k2).colTo hS (n + 1) (spIn n m C T 0 φ) (.cpl h) =
      ∑ al : (F n).β, (k1 al).op (hF n al) (kk.colTo hF n φ al) := by
  show (∑ b : (spFam F n m C T n).β, ((spKer kk k1 k2 n b (.cpl h)).opOf (hS n b) _) ∘ₗ (LinearMap.proj b)) _ = _
  rw [LinearMap.sum_apply]
  refine (Fintype.sum_equiv (SpIdx.lowEquiv (β := fun j => (F j).β) hm le_rfl) _ _ fun b => ?_).symm
  exact congrArg ((k1 b).opOf (hF n b) ((F n).mem b).outSec) (spKer_colTo_low kk k1 k2 hm hF φ n le_rfl b).symm

theorem spKer_colTo_top (hm : m = n + 2) (hF : ∀ i, (F i).Ok) (hC : C.gsd.Ok) (φ : (F 0).Forms) (h : m = m) :
    (spKer kk k1 k2).colTo hS m (spIn n m C T 0 φ) (.top h) =
      k2.op hC (∑ al : (F n).β, (k1 al).op (hF n al) (kk.colTo hF n φ al)) := by
  subst hm
  show (∑ b : (spFam F n (n + 2) C T (n + 1)).β, ((spKer kk k1 k2 (n + 1) b (.top h)).opOf (hS (n + 1) b) _) ∘ₗ (LinearMap.proj b)) _ = _
  rw [LinearMap.sum_apply, Fintype.sum_eq_single (SpIdx.cpl rfl) fun b hb => absurd (SpIdx.eq_cpl (by omega) rfl b) hb]
  exact congrArg (k2.op hC) (spKer_colTo_cpl kk k1 k2 (by omega) hF φ rfl)

end Splice

theorem spKer_colTo_eq_colCpl {F : ℕ → GFam K} {n m : ℕ} (hm : m = n + 2) (hF : ∀ i, (F i).Ok) {b : (F (n + 1)).β}
    {Y : Cpl ((F (n + 1)).mem b)} {T : MemOn (F m)} (kk : KerFam F)
    (k1 : ∀ al : (F n).β, ClsKer ((F n).mem al) (MemOn.pairs (F (n + 1)) b Y).gsd) (k2 : ClsKer (MemOn.pairs (F (n + 1)) b Y).gsd T.gsd)
    (hS : ∀ i, (spFam F n m (MemOn.pairs (F (n + 1)) b Y) T i).Ok) {S₁ : GSD K}
    (A : ∀ al : (F n).β, CplKer ((F n).mem al) ((F (n + 1)).mem b) S₁ Y) (til : S₁.D → T.D) (e : (F m).V →ₗ[K] S₁.V)
    (h1 : ∀ al d₀ (d : Y.Pts), (A al).k1 d₀ d.1.1 d.1.2 = (k1 al).k d₀ d)
    (h2 : ∀ al (d : Y.Pts) d₁, (A al).k2 d.1.1 d.1.2 d₁ = e ∘ₗ k2.k d (til d₁)) (φ : (F 0).Forms) (h : m = m) (d₁ : S₁.D) :
    e (((spKer kk k1 k2).colTo hS m (spIn n m _ T 0 φ) (.top h)).1 (til d₁)) = (colCpl kk hF n A (hF (n + 1) b) φ).1 d₁ := by
  have hC := cplGSD_ok Y (hF (n + 1) b)
  rw [spKer_colTo_top kk k1 k2 hm hF hC φ h, map_sum]
  show _ = ((∑ al : (F n).β, (((A al).comp (hF (n + 1) b) ((F (n + 1)).mem b).outSec).op (hF n al)) ∘ₗ (LinearMap.proj al))
    (kk.colTo hF n φ)).1 d₁
  rw [LinearMap.sum_apply, Submodule.coe_sum, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun al _ => ?_
  obtain ⟨h', l1, l2, e1, e2, e3⟩ := cpl_op_eq_comp (A al) (hF n al) (hF (n + 1) b)
  have e4 : l1 = k1 al := by
    obtain ⟨a, ha⟩ := l1
    have : a = (k1 al).k := funext fun d₀ => funext fun d => (e1 d₀ d).trans (h1 al d₀ d)
    subst this
    rfl
  rw [LinearMap.comp_apply, e3, e4]
  show e (k2.appOf hC _ _ (til d₁)) = l2.appOf hC _ _ d₁
  unfold ClsKer.appOf
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, e2, h2]
  rfl

end GlobalTheory.GO
