import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum Formalism.IndefR.Lev
open scoped TensorProduct ComplexOrder
open Classical

namespace Formalism.IndefR.NX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure ExpSet (D : D7) where

  ψ : AddChar (AF D.host.F) ℂ

  θ : InfFam D

  V : HSp D

  W : HSp D

  sV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ

  BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ
  pV : D.what₂.Tau → ℕ
  pW : D.what₂.Tau → ℕ

  ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)

  βV : GL (Fin V.rank) (Formalism.IndefR.Datum.EAf D)
  βW : GL (Fin W.rank) (Formalism.IndefR.Datum.EAf D)

  χV : (AE D)ˣ →* Circle
  χW : (AE D)ˣ →* Circle

  om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)

  f₀ : WO V W → ℂ

  gp : Fin 2 → ℕ
  pb : Fin 2 → 𝓞 D.host.E

  Pg : Finset (Formalism.L2.DIV.Pl D.host.E)

  Pd : Finset (Formalism.L2.DIV.Pl D.host.E)

  l : ℕ
  Pl : Finset (Formalism.L2.DIV.Pl D.host.E)

  pde : Fin 2 → ℕ

  e0 : AE D

  Φ0 : WO V W → ℂ

  φ0 : WO V W → ℂ

  ψg : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ

  fr : Formalism.IndefR.Lev.Frm
  posV : ∀ τ, (gramAt D V τ).PosDef
  cartV : ∀ τ, IsCartanInv (gramAt D V τ) (sV τ)
  cartW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)
  onbV : ∀ τ, IsONBasis (gramAt D V τ) (sV τ) (BV τ) (pV τ)
  onbW : ∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) (pW τ)
  frV : Formalism.L2.DIV.IsFrame βV ΛV
  frW : Formalism.L2.DIV.IsFrame βW ΛW
  sdV : IsSelfDualC V ΛV
  sdW : IsSelfDualC W ΛW
  weil : IsWeilDatumO ψ V W χV χW om
  vac : IsVacO ψ θ V W sV sW ΛV ΛW f₀
  typePl : IsTypePlaces (D := D) gp pb Pg
  genPsi : Formalism.L2.DIV.IsGenericPsi Pg ψg
  lPl : ∀ PP : Formalism.L2.DIV.Pl D.host.E, PP ∈ Pl ↔ ((l : 𝓞 D.host.E) ∈ PP.asIdeal)
  idempotent_sum : IsIdemSum e0 (Pg ∪ Pd)
  φ0_vec : IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e0) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ0 φ0

namespace ExpSet

variable (S : ExpSet D)

def LW : Formalism.L2.DIV.LevDat D.host.E ℂ S.W.rank :=
  datW (D := D) S.W.rank S.Pg (Formalism.L2.DIV.P0 S.Pg S.W.rank S.ψg) S.fr

def KV : Subgroup (GA D S.V) := levA S.V (Formalism.L2.DIV.Kg D.sp.cm S.V.gram S.βV ∅)

def fock (f : WO S.V S.W → ℂ) : MvPolynomial (FVar D S.W.rank S.V.rank) ℂ →ₗ[ℂ] (WO S.V S.W → ℂ) :=
  pureTensorO S.ψ S.θ S.V S.W S.sV S.sW S.BV S.BW f

end ExpSet

def SplitLevPl (S : ExpSet D) (PP : Formalism.L2.DIV.Pl D.host.E) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.Coprime p S.l ∧ (∀ i, p ≠ S.pde i) ∧ D.host.cls p = .splitK ∧
    ((p : 𝓞 D.host.E) ∈ PP.asIdeal)

theorem natCast_not_mem_of_coprime {PP : Formalism.L2.DIV.Pl D.host.E} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : (m : 𝓞 D.host.E) ∈ PP.asIdeal) : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hmn
  have e : (a : 𝓞 D.host.E) * (m : 𝓞 D.host.E) + (b : 𝓞 D.host.E) * (n : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
    push_cast at this
    exact this
  have h1 : (1 : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← e]
    exact PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ hm) (PP.asIdeal.mul_mem_left _ hn)
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem SplitLevPl.not_mem_Pl {S : ExpSet D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : SplitLevPl S PP) : PP ∉ S.Pl := by
  intro hl
  obtain ⟨p, -, -, hcop, -, -, hp⟩ := h
  exact natCast_not_mem_of_coprime hcop hp ((S.lPl PP).1 hl)

theorem SplitLevPl.two_not_mem {S : ExpSet D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : SplitLevPl S PP) :
    (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
  obtain ⟨p, hp, h2, -, -, -, hpm⟩ := h
  have hc : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 h2
  have := natCast_not_mem_of_coprime hc hpm
  exact_mod_cast this

theorem SplitLevPl.conjPl {S : ExpSet D} {PP : Formalism.L2.DIV.Pl D.host.E} (h : SplitLevPl S PP) :
    SplitLevPl S (Formalism.L2.DIV.conjPl PP) := by
  obtain ⟨p, hp, h2, hc, hde, hk, hm⟩ := h
  refine ⟨p, hp, h2, hc, hde, hk, ?_⟩
  exact (Formalism.L2.DIV.isConjPl_conjPl PP (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).1 hm

theorem isConjPl_conjPl (PP : Formalism.L2.DIV.Pl D.host.E) : IsConjPl (D := D) PP (Formalism.L2.DIV.conjPl PP) :=
  fun c hc => ⟨Formalism.L2.DIV.starO c,
    (Formalism.L2.DIV.isConjPl_conjPl PP c (Formalism.L2.DIV.starO c) (Formalism.L2.DIV.starO_coe c)).1 hc, Formalism.L2.DIV.starO_coe c⟩

def HasLevelType (S : ExpSet D) (f : WO S.V S.W → ℂ) : Prop :=
  ∀ κ ∈ levG S.W S.βW S.LW, S.om (1, κ) f = levChi S.W S.βW S.LW κ • f

structure CoefLat (S : ExpSet D) (O : Type) [CommRing O] where
  ι : O →+* ℂ
  Cf : Type
  [acg : AddCommGroup Cf]
  [md : Module O Cf]
  LL : GA D S.V → Submodule O Cf
  act : GA D S.V → (Cf ≃ₗ[O] Cf)
  rd : Cf →+ MvPolynomial (FVar D S.W.rank S.V.rank) ℂ
  rd_smul : ∀ (a : O) (x : Cf), rd (a • x) = MvPolynomial.C (ι a) * rd x
  LL_left : ∀ γ ∈ GQ S.V, ∀ h, (LL h).map (act γ).toLinearMap = LL (γ * h)
  LL_right : ∀ h, ∀ k ∈ S.KV, LL (h * k) = LL h

attribute [instance] CoefLat.acg CoefLat.md

def eTot (S : ExpSet D) (P1 : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D) : AE D :=
  S.e0 + ∑ PP ∈ P1, es PP

section SuppHalf

variable {m n : ℕ}

def offHalf (e : AE D) : Submodule ℂ (Mx D m n → ℂ) where
  carrier := {g | ∀ t, ¬ IsHalf e t → g t = 0}
  add_mem' := by
    intro a b ha hb t ht
    simp [ha t ht, hb t ht]
  zero_mem' := by intro t _; rfl
  smul_mem' := by
    intro c a ha t ht
    simp [ha t ht]

theorem isHalf_of_add {e : AE D} {t x : Mx D m n} (h : IsHalf e (t + x)) (hx : IsHalf e x) : IsHalf e t := by
  intro i j
  have h1 := h i j
  have h2 := hx i j
  simp only [Matrix.add_apply, mul_add] at h1
  rw [h2] at h1
  exact add_right_cancel h1

theorem isThetaAt_supp_half {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ}
    {f₀ Φ f : Mx D m n → ℂ} (h : IsThetaAt ψ B hs e Λ c f₀ Φ f) : ∀ t, ¬ IsHalf e t → Φ t = 0 := by
  classical
  by_contra hne
  have hΦ : Φ ∉ offHalf (D := D) (m := m) (n := n) e := hne
  obtain ⟨⟨T, hT⟩, hf⟩ := h
  have hq : (offHalf (D := D) (m := m) (n := n) e).mkQ Φ ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ ((Mx D m n → ℂ) ⧸ offHalf (D := D) (m := m) (n := n) e),
      φ ((offHalf (D := D) (m := m) (n := n) e).mkQ Φ) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  let lam : (Mx D m n → ℂ) →ₗ[ℂ] ℂ := φ ∘ₗ (offHalf (D := D) (m := m) (n := n) e).mkQ
  have hlam : ∀ g ∈ offHalf (D := D) (m := m) (n := n) e, lam g = 0 := by
    intro g hg
    simp [lam, (Submodule.Quotient.mk_eq_zero _).2 hg]
  let T1 : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) := T + lam.smulRight (fun _ => (1 : ℂ))
  have hT1 : ∀ g ∈ offHalf (D := D) (m := m) (n := n) e, T1 g = T g := by
    intro g hg
    simp [T1, hlam g hg]
  have hSB : ∀ Φ', IsSBHalf e Λ Φ' → Φ' ∈ offHalf (D := D) (m := m) (n := n) e := by
    intro Φ' h t ht
    by_contra h0
    exact ht (h.1 t h0)
  have hP1 : IsPlaceModel ψ B hs e Λ c f₀ T1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro Φ' hΦ' x hx
      have hm : (fun t => Φ' (t + x)) ∈ offHalf (D := D) (m := m) (n := n) e := by
        intro t ht
        by_contra h0
        exact ht (isHalf_of_add (hΦ'.1 _ h0) hx)
      rw [hT1 _ hm, hT1 _ (hSB _ hΦ'), hT.trans Φ' hΦ' x hx]
    · intro Φ' hΦ' y hy
      have hm : (fun t => ψ (B t y) * Φ' t) ∈ offHalf (D := D) (m := m) (n := n) e := by
        intro t ht
        simp [hSB _ hΦ' t ht]
      rw [hT1 _ hm, hT1 _ (hSB _ hΦ'), hT.modul Φ' hΦ' y hy]
    · have hm : c • halfInd e Λ ∈ offHalf (D := D) (m := m) (n := n) e := by
        intro t ht
        simp [halfInd, ht]
      rw [hT1 _ hm, hT.vac]
  have e1 := hf T hT
  have e2 := hf T1 hP1
  have h3 : T1 Φ = T Φ := by rw [← e1, ← e2]
  have h4 := congrFun h3 0
  simp [T1, lam] at h4
  exact hφ h4

end SuppHalf

theorem ExpSet.Φ0_offHalf (S : ExpSet D) : ∀ x, ¬ IsHalf (cA D S.e0) x → S.Φ0 x = 0 :=
  isThetaAt_supp_half S.φ0_vec

def PhiTot (S : ExpSet D) (P1 : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D)
    (Φl : Formalism.L2.DIV.Pl D.host.E → WO S.V S.W → ℂ) (x : WO S.V S.W) : ℂ :=
  if IsHalf (cA D (eTot S P1 es)) x then S.Φ0 (x.map (cA D S.e0 * ·)) * ∏ PP ∈ P1, Φl PP x else 0

theorem phiTot_empty (S : ExpSet D) (es : Formalism.L2.DIV.Pl D.host.E → AE D)
    (Φl : Formalism.L2.DIV.Pl D.host.E → WO S.V S.W → ℂ) : PhiTot S ∅ es Φl = S.Φ0 := by
  funext x
  simp only [PhiTot, eTot, Finset.sum_empty, add_zero, Finset.prod_empty, mul_one]
  split_ifs with h
  · congr 1
    ext i j
    simp [Matrix.map_apply, h i j]
  · exact (S.Φ0_offHalf x h).symm

structure RawDat (S : ExpSet D) {O : Type} [CommRing O] (C : CoefLat S O) where
  h : GA D S.V
  Ph : Finset (Formalism.L2.DIV.Pl D.host.E)
  eh : AE D
  hP : GA D S.V
  k : GA D S.V
  eh_idem : IsIdemSum eh Ph
  hP_mem_gfC : hP ∈ GfC S.V
  hP_supp : SuppAt eh S.V hP
  Ph_lev : ∀ PP ∈ Ph, SplitLevPl S PP
  Ph_disj : Disjoint Ph (S.Pg ∪ S.Pd)
  Ph_conj : ∀ PP ∈ Ph, ∀ QQ ∈ S.Pg ∪ S.Pd, ¬ IsConjPl (D := D) PP QQ
  k_mem : k ∈ S.KV
  h_eq : h = hP * k
  P : C.Cf
  P_mem : P ∈ C.LL h
  P1 : Finset (Formalism.L2.DIV.Pl D.host.E)
  es : Formalism.L2.DIV.Pl D.host.E → AE D
  Φl : Formalism.L2.DIV.Pl D.host.E → WO S.V S.W → ℂ
  φ : WO S.V S.W → ℂ
  es_at : ∀ PP ∈ P1, Formalism.L2.NTheta.IsIdemAt (es PP) PP
  e_idem : IsIdemSum (eTot S P1 es) (S.Pg ∪ S.Pd ∪ P1)
  disjoint_split_level_places : Disjoint P1 (S.Pg ∪ S.Pd ∪ S.Pl)
  split_level_places : ∀ PP ∈ P1, SplitLevPl S PP
  Φl_loc : ∀ PP ∈ P1, ∀ x : WO S.V S.W, Φl PP x = Φl PP (x.map (cA D (es PP) * ·))
  val0 : ∀ x, ∃ a : O, S.Φ0 x = C.ι a
  Rl : Subring ℂ
  Φl_O : ∀ PP ∈ P1, ∀ x, Φl PP x ∈ Rl
  vec : IsThetaAt S.ψ (symplO S.V S.W) (heisO S.ψ S.V S.W) (cA D (eTot S P1 es))
    (latO S.V S.W S.ΛV S.ΛW fun _ => True) 1 S.f₀ (PhiTot S P1 es Φl) φ

structure Dat (S : ExpSet D) {O : Type} [CommRing O] (C : CoefLat S O) extends RawDat S C where
  typ : HasLevelType S φ
  Rl_O : Rl = C.ι.range

variable {S : ExpSet D} {O : Type} [CommRing O] {C : CoefLat S O}

namespace RawDat

def levOne (d : RawDat S C) : Finset (Formalism.L2.DIV.Pl D.host.E) := S.Pg ∪ S.Pd ∪ d.P1 ∪ d.Ph

def lev (d : RawDat S C) : Finset (Formalism.L2.DIV.Pl D.host.E) := d.levOne ∪ d.levOne.image Formalism.L2.DIV.conjPl

def loc (d : RawDat S C) (PP : Formalism.L2.DIV.Pl D.host.E) : WO S.V S.W → ℂ :=
  if PP ∈ d.P1 then d.Φl PP else fun _ => 1

def serK (d : RawDat S C) (g : GA D S.W) : ℂ :=
  thetaKO S.om d.h g (S.fock d.φ (C.rd d.P))

def esR (d : RawDat S C) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (eQ : Formalism.L2.DIV.Pl D.host.E → AE D)
    (PP : Formalism.L2.DIV.Pl D.host.E) : AE D :=
  if PP ∈ Q then eQ PP else d.es PP

def ΦlR (d : RawDat S C) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ΦQ : Formalism.L2.DIV.Pl D.host.E → WO S.V S.W → ℂ)
    (PP : Formalism.L2.DIV.Pl D.host.E) : WO S.V S.W → ℂ :=
  if PP ∈ Q then ΦQ PP else d.Φl PP

def repl (d : RawDat S C) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (eQ : Formalism.L2.DIV.Pl D.host.E → AE D)
    (ΦQ : Formalism.L2.DIV.Pl D.host.E → WO S.V S.W → ℂ)
    (hdisj : Disjoint Q (S.Pg ∪ S.Pd ∪ S.Pl))
    (hlev : ∀ PP ∈ Q, SplitLevPl S PP)
    (hat : ∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (eQ PP) PP)
    (hidem : IsIdemSum (eTot S (d.P1 ∪ Q) (d.esR Q eQ)) (S.Pg ∪ S.Pd ∪ (d.P1 ∪ Q)))
    (hloc : ∀ PP ∈ Q, ∀ x : WO S.V S.W, ΦQ PP x = ΦQ PP (x.map (cA D (eQ PP) * ·)))
    (R' : Subring ℂ) (hO : ∀ PP ∈ Q, ∀ x, ΦQ PP x ∈ R')
    (φ' : WO S.V S.W → ℂ)
    (hvec : IsThetaAt S.ψ (symplO S.V S.W) (heisO S.ψ S.V S.W) (cA D (eTot S (d.P1 ∪ Q) (d.esR Q eQ)))
      (latO S.V S.W S.ΛV S.ΛW fun _ => True) 1 S.f₀ (PhiTot S (d.P1 ∪ Q) (d.esR Q eQ) (d.ΦlR Q ΦQ)) φ') : RawDat S C where
  h := d.h
  Ph := d.Ph
  eh := d.eh
  hP := d.hP
  k := d.k
  eh_idem := d.eh_idem
  hP_mem_gfC := d.hP_mem_gfC
  hP_supp := d.hP_supp
  Ph_lev := d.Ph_lev
  Ph_disj := d.Ph_disj
  Ph_conj := d.Ph_conj
  k_mem := d.k_mem
  h_eq := d.h_eq
  P := d.P
  P_mem := d.P_mem
  P1 := d.P1 ∪ Q
  es := d.esR Q eQ
  Φl := d.ΦlR Q ΦQ
  φ := φ'
  es_at PP hPP := by
    unfold esR
    by_cases hq : PP ∈ Q
    · rw [if_pos hq]; exact hat PP hq
    · rw [if_neg hq]; exact d.es_at PP ((Finset.mem_union.1 hPP).resolve_right hq)
  e_idem := hidem
  disjoint_split_level_places := Finset.disjoint_union_left.2 ⟨d.disjoint_split_level_places, hdisj⟩
  split_level_places PP hPP := by
    rcases Finset.mem_union.1 hPP with h | h
    · exact d.split_level_places PP h
    · exact hlev PP h
  Φl_loc PP hPP x := by
    unfold ΦlR esR
    by_cases hq : PP ∈ Q
    · rw [if_pos hq, if_pos hq]; exact hloc PP hq x
    · rw [if_neg hq, if_neg hq]; exact d.Φl_loc PP ((Finset.mem_union.1 hPP).resolve_right hq) x
  val0 := d.val0
  Rl := d.Rl ⊔ R'
  Φl_O PP hPP x := by
    unfold ΦlR
    by_cases hq : PP ∈ Q
    · rw [if_pos hq]; exact (le_sup_right : R' ≤ d.Rl ⊔ R') (hO PP hq x)
    · rw [if_neg hq]; exact (le_sup_left : d.Rl ≤ d.Rl ⊔ R') (d.Φl_O PP ((Finset.mem_union.1 hPP).resolve_right hq) x)
  vec := hvec

theorem Ph_disj_Pl (d : RawDat S C) : Disjoint d.Ph S.Pl :=
  Finset.disjoint_left.2 fun _ hPP => (d.Ph_lev _ hPP).not_mem_Pl

theorem two_not_mem_lev (d : RawDat S C) {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ d.P1 ∪ d.Ph) :
    (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
  rcases Finset.mem_union.1 h with h | h
  · exact (d.split_level_places PP h).two_not_mem
  · exact (d.Ph_lev PP h).two_not_mem

theorem levOne_split (d : RawDat S C) {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ d.levOne) (h' : PP ∉ S.Pg ∪ S.Pd) :
    SplitLevPl S PP := by
  unfold levOne at h
  rcases Finset.mem_union.1 h with h | h
  · rcases Finset.mem_union.1 h with h | h
    · exact absurd h h'
    · exact d.split_level_places PP h
  · exact d.Ph_lev PP h

theorem lev_split (d : RawDat S C) {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ d.lev)
    (h' : PP ∉ (S.Pg ∪ S.Pd) ∪ (S.Pg ∪ S.Pd).image Formalism.L2.DIV.conjPl) : SplitLevPl S PP := by
  unfold lev at h
  rcases Finset.mem_union.1 h with h | h
  · exact d.levOne_split h fun h0 => h' (Finset.mem_union_left _ h0)
  · obtain ⟨QQ, hQ, rfl⟩ := Finset.mem_image.1 h
    exact (d.levOne_split hQ fun h0 => h' (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h0))).conjPl

theorem conjPl_mem_lev (d : RawDat S C) {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ d.lev) :
    Formalism.L2.DIV.conjPl PP ∈ d.lev := by
  unfold lev at h ⊢
  rcases Finset.mem_union.1 h with h | h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  · obtain ⟨QQ, hQ, rfl⟩ := Finset.mem_image.1 h
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact Finset.mem_union_left _ hQ

end RawDat

theorem isThetaAt_unique {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ}
    {f₀ Φ f f' : Mx D m n → ℂ} (h : IsThetaAt ψ B hs e Λ c f₀ Φ f) (h' : IsThetaAt ψ B hs e Λ c f₀ Φ f') : f = f' := by
  obtain ⟨⟨T, hT⟩, hf⟩ := h
  rw [hf T hT, h'.2 T hT]

section ReplLemmas

variable (d : RawDat S C) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (eQ : Formalism.L2.DIV.Pl D.host.E → AE D)
  (ΦQ : Formalism.L2.DIV.Pl D.host.E → WO S.V S.W → ℂ)
  (hdisj : Disjoint Q (S.Pg ∪ S.Pd ∪ S.Pl))
  (hlev : ∀ PP ∈ Q, SplitLevPl S PP)
  (hat : ∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (eQ PP) PP)
  (hidem : IsIdemSum (eTot S (d.P1 ∪ Q) (d.esR Q eQ)) (S.Pg ∪ S.Pd ∪ (d.P1 ∪ Q)))
  (hloc : ∀ PP ∈ Q, ∀ x : WO S.V S.W, ΦQ PP x = ΦQ PP (x.map (cA D (eQ PP) * ·)))
  (R' : Subring ℂ) (hO : ∀ PP ∈ Q, ∀ x, ΦQ PP x ∈ R')
  (φ' : WO S.V S.W → ℂ)
  (hvec : IsThetaAt S.ψ (symplO S.V S.W) (heisO S.ψ S.V S.W) (cA D (eTot S (d.P1 ∪ Q) (d.esR Q eQ)))
      (latO S.V S.W S.ΛV S.ΛW fun _ => True) 1 S.f₀ (PhiTot S (d.P1 ∪ Q) (d.esR Q eQ) (d.ΦlR Q ΦQ)) φ')

theorem RawDat.repl_loc_off (PP : Formalism.L2.DIV.Pl D.host.E) (hq : PP ∉ Q) :
    (d.repl Q eQ ΦQ hdisj hlev hat hidem hloc R' hO φ' hvec).loc PP = d.loc PP := by
  unfold RawDat.loc RawDat.repl RawDat.ΦlR
  simp only [Finset.mem_union, hq, or_false, if_false]

theorem RawDat.repl_loc_on (PP : Formalism.L2.DIV.Pl D.host.E) (hq : PP ∈ Q) :
    (d.repl Q eQ ΦQ hdisj hlev hat hidem hloc R' hO φ' hvec).loc PP = ΦQ PP := by
  unfold RawDat.loc RawDat.repl RawDat.ΦlR
  simp only [Finset.mem_union, hq, or_true, if_true]

theorem RawDat.repl_levOne : (d.repl Q eQ ΦQ hdisj hlev hat hidem hloc R' hO φ' hvec).levOne = d.levOne ∪ Q := by
  unfold RawDat.levOne RawDat.repl
  ext x
  simp only [Finset.mem_union]
  tauto

theorem RawDat.repl_lev : (d.repl Q eQ ΦQ hdisj hlev hat hidem hloc R' hO φ' hvec).lev =
    d.lev ∪ (Q ∪ Q.image Formalism.L2.DIV.conjPl) := by
  simp only [RawDat.lev, RawDat.repl_levOne, Finset.image_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem RawDat.repl_h : (d.repl Q eQ ΦQ hdisj hlev hat hidem hloc R' hO φ' hvec).h = d.h := rfl

theorem RawDat.repl_P : (d.repl Q eQ ΦQ hdisj hlev hat hidem hloc R' hO φ' hvec).P = d.P := rfl

theorem RawDat.repl_empty_phi (hvec0 : IsThetaAt S.ψ (symplO S.V S.W) (heisO S.ψ S.V S.W)
      (cA D (eTot S (d.P1 ∪ ∅) (d.esR ∅ eQ))) (latO S.V S.W S.ΛV S.ΛW fun _ => True) 1 S.f₀
      (PhiTot S (d.P1 ∪ ∅) (d.esR ∅ eQ) (d.ΦlR ∅ ΦQ)) φ') : φ' = d.φ := by
  have he : eTot S (d.P1 ∪ ∅) (d.esR ∅ eQ) = eTot S d.P1 d.es := by
    simp [eTot, RawDat.esR]
  have hes : d.esR ∅ eQ = d.es := by funext PP; simp [RawDat.esR]
  have hΦl : d.ΦlR ∅ ΦQ = d.Φl := by funext PP; simp [RawDat.ΦlR]
  have hΦ : PhiTot S (d.P1 ∪ ∅) (d.esR ∅ eQ) (d.ΦlR ∅ ΦQ) = PhiTot S d.P1 d.es d.Φl := by
    rw [hes, hΦl, Finset.union_empty]
  rw [he, hΦ] at hvec0
  exact isThetaAt_unique hvec0 d.vec

end ReplLemmas

theorem thetaKO_law {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (h : GA D V) (g κ : GA D W)
    (f : WO V W → ℂ) (c : ℂ) (hf : om (1, κ) f = c • f) : thetaKO om h (g * κ) f = c * thetaKO om h g f := by
  unfold thetaKO
  have e : ((h, g * κ) : GA D V × GA D W) = (h, g) * (1, κ) := Prod.ext (mul_one h).symm rfl
  rw [e, map_mul, Module.End.mul_apply, hf, map_smul]
  rfl

def FockFinComm (S : ExpSet D) : Prop :=
  ∀ κ ∈ GfC S.W, ∀ (f : WO S.V S.W → ℂ) (c : ℂ) (Pp : MvPolynomial (FVar D S.W.rank S.V.rank) ℂ),
    S.om (1, κ) f = c • f → S.om (1, κ) (S.fock f Pp) = c • S.fock f Pp

theorem levG_fin {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Datum.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}
    {κ : GA D V} (hκ : κ ∈ levG V β L) : κ ∈ GfC V :=
  (Subgroup.mem_inf.1 hκ).1

theorem Dat.serK_type (hF : FockFinComm S) (d : Dat S C) (κ : GA D S.W) (hκ : κ ∈ levG S.W S.βW S.LW)
    (g : GA D S.W) : d.toRawDat.serK (g * κ) = levChi S.W S.βW S.LW κ * d.toRawDat.serK g :=
  thetaKO_law _ _ _ _ _ _ (hF κ (levG_fin hκ) _ _ _ (d.typ κ hκ))

def BaseVectorHasType (S : ExpSet D) : Prop := HasLevelType S S.φ0

def BaseValO (S : ExpSet D) (C : CoefLat S O) : Prop := ∀ x, ∃ a : O, S.Φ0 x = C.ι a

def Dat.base (hT : BaseVectorHasType S) (hO : BaseValO S C) (Ph : Finset (Formalism.L2.DIV.Pl D.host.E)) (eh : AE D)
    (hP k : GA D S.V) (heh : IsIdemSum eh Ph) (hfin : hP ∈ GfC S.V) (hsupp : SuppAt eh S.V hP)
    (hlev : ∀ PP ∈ Ph, SplitLevPl S PP) (hdj : Disjoint Ph (S.Pg ∪ S.Pd))
    (hcj : ∀ PP ∈ Ph, ∀ QQ ∈ S.Pg ∪ S.Pd, ¬ IsConjPl (D := D) PP QQ) (hk : k ∈ S.KV)
    (P : C.Cf) (hPm : P ∈ C.LL (hP * k)) : Dat S C where
  h := hP * k
  Ph := Ph
  eh := eh
  hP := hP
  k := k
  eh_idem := heh
  hP_mem_gfC := hfin
  hP_supp := hsupp
  Ph_lev := hlev
  Ph_disj := hdj
  Ph_conj := hcj
  k_mem := hk
  h_eq := rfl
  P := P
  P_mem := hPm
  P1 := ∅
  es := fun _ => 0
  Φl := fun _ _ => 1
  φ := S.φ0
  es_at _ h := absurd h (Finset.notMem_empty _)
  e_idem := by simp only [eTot, Finset.sum_empty, add_zero, Finset.union_empty]; exact S.idempotent_sum
  disjoint_split_level_places := Finset.disjoint_empty_left _
  split_level_places _ h := absurd h (Finset.notMem_empty _)
  Φl_loc _ _ _ := rfl
  val0 := hO
  Rl := C.ι.range
  Φl_O _ h := absurd h (Finset.notMem_empty _)
  vec := by
    rw [phiTot_empty]
    simp only [eTot, Finset.sum_empty, add_zero]
    exact S.φ0_vec
  typ := hT
  Rl_O := rfl

theorem isIdemSum_zero : IsIdemSum (0 : AE D) ∅ :=
  ⟨⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩, zero_mul _⟩

theorem suppAt_zero_one (V : HSp D) : SuppAt (0 : AE D) V 1 := by
  intro i j
  have h1 : Formalism.L2.Theta.mt V 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  rw [h1, sub_self]
  simp

theorem dat_nonempty (hT : BaseVectorHasType S) (hO : BaseValO S C) : Nonempty (Dat S C) :=
  ⟨Dat.base hT hO ∅ 0 1 1 isIdemSum_zero (Subgroup.one_mem _) (suppAt_zero_one S.V)
    (fun _ h => absurd h (Finset.notMem_empty _)) (Finset.disjoint_empty_left _)
    (fun _ h => absurd h (Finset.notMem_empty _)) (Subgroup.one_mem _) 0 (Submodule.zero_mem _)⟩

theorem exists_base (hT : BaseVectorHasType S) (hO : BaseValO S C) (Ph : Finset (Formalism.L2.DIV.Pl D.host.E)) (eh : AE D)
    (hP k : GA D S.V) (heh : IsIdemSum eh Ph) (hfin : hP ∈ GfC S.V) (hsupp : SuppAt eh S.V hP)
    (hlev : ∀ PP ∈ Ph, SplitLevPl S PP) (hdj : Disjoint Ph (S.Pg ∪ S.Pd))
    (hcj : ∀ PP ∈ Ph, ∀ QQ ∈ S.Pg ∪ S.Pd, ¬ IsConjPl (D := D) PP QQ) (hk : k ∈ S.KV)
    (P : C.Cf) (hPm : P ∈ C.LL (hP * k)) :
    ∃ d : Dat S C, d.h = hP * k ∧ d.P = P ∧ d.φ = S.φ0 ∧
      d.toRawDat.lev = (S.Pg ∪ S.Pd ∪ Ph) ∪ (S.Pg ∪ S.Pd ∪ Ph).image Formalism.L2.DIV.conjPl :=
  ⟨Dat.base hT hO Ph eh hP k heh hfin hsupp hlev hdj hcj hk P hPm, rfl, rfl, rfl, by
    simp [RawDat.lev, RawDat.levOne, Dat.base]⟩

def ClassesSplit (S : ExpSet D) : Prop :=
  ∀ h ∈ GfC S.V, ∃ γ ∈ GQ S.V, ∃ (Ph : Finset (Formalism.L2.DIV.Pl D.host.E)) (eh : AE D) (hP k : GA D S.V),
    IsIdemSum eh Ph ∧ hP ∈ GfC S.V ∧ SuppAt eh S.V hP ∧ (∀ PP ∈ Ph, SplitLevPl S PP) ∧ Disjoint Ph (S.Pg ∪ S.Pd) ∧
    (∀ PP ∈ Ph, ∀ QQ ∈ S.Pg ∪ S.Pd, ¬ IsConjPl (D := D) PP QQ) ∧ k ∈ S.KV ∧ h = γ * (hP * k)

def RawDat.levConj (d : RawDat S C) : Set (Formalism.L2.DIV.Pl D.host.E) :=
  {PP | ∃ QQ ∈ d.lev, PP = QQ ∨ IsConjPl (D := D) PP QQ}

def CoefLat.triv (S : ExpSet D) (O : Type) [CommRing O] (ι : O →+* ℂ) : CoefLat S O where
  ι := ι
  Cf := O
  LL _ := ⊤
  act _ := LinearEquiv.refl O O
  rd := 0
  rd_smul _ _ := by simp
  LL_left _ _ _ := by simp
  LL_right _ _ _ := rfl

end Formalism.IndefR.NX
