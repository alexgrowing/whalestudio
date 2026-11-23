import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

namespace GlobalTheory.TilClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open GlobalTheory.TopStep (sumE prH extI redGL)

section Points

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem glint_of_sumE {P : HeightOneSpectrum (𝓞 E)} {g : Sp E n ≃ₗ[E] Sp E n} (h : sumE hN g 1 ∈ GLint E N P) :
    g ∈ GLint E n P := fun x => by
  let y : Sp E N := fun l => if hl : l.1 < n then x ⟨l.1, hl⟩ else 0
  have y1 : prH E hN y = x := funext fun i => dif_pos i.2
  have y2 : y (Br.iL hN) = 0 := dif_neg (lt_irrefl _)
  have h2 := h y
  rw [TopStep.mem_stdAt_succ hN, TopStep.mem_stdAt_succ hN, TopStep.prH_sumE, TopStep.sumE_last, y1, y2, mul_zero] at h2
  exact (and_congr_left_iff.1 h2) TopStep.intAt_zero

theorem sumE_pass (f f' γ : Sp E n ≃ₗ[E] Sp E n) (t : Eˣ) :
    (sumE hN f' t)⁻¹ * sumE hN γ 1 * sumE hN f t = sumE hN (f'⁻¹ * γ * f) 1 := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul, ← TopStep.sumE_mul, ← TopStep.sumE_mul, one_mul, mul_one, mul_assoc,
    mul_inv_cancel_left]

variable (hconj : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
  (hbig : 2 ^ Module.finrank ℚ E < ∏ P ∈ ST, Ideal.absNorm P.asIdeal) {pi : 𝓞 E}
  (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
include hconj hbig hT hG

theorem exists_ext_deco (d₁ d₂ : DecoSet E n ∅ SG) (γ : UF E N) (k : GLG E N SG)
    (H : (γ, k) • DecoSet.tilH (ST := ST) hN pi d₁ = DecoSet.tilH (ST := ST) hN pi d₂) :
    ∃ (γ' : UF E n) (h : GLG E n SG), γ = extUH hN γ' ∧ k = extGH hN h ∧ (γ', h) • d₁ = d₂ := by
  have H0 : (DecoSet.tilH (ST := ST) hN pi d₁).1.act γ.1 k = (DecoSet.tilH (ST := ST) hN pi d₂).1 := congrArg Subtype.val H
  obtain ⟨γ', rfl⟩ : ∃ γ' : UF E n, γ = extUH hN γ' := by
    subst hN
    have H1 : (DecoSet.til (ST := ST) pi d₁).1.act γ.1 k = (DecoSet.til (ST := ST) pi d₂).1 := H0
    rw [DecoSet.til_val _ hT hG, DecoSet.til_val _ hT hG] at H1
    exact exists_extU_of_fix γ (til_fix_eLast hconj hbig hT γ.2 H1)
  have key : ∀ w : SG, ∃ h, k w = diagEmb _ (by omega : n ≤ N) h := fun w => by
    have h1 := TopStep.isLiftFr_tilH hN d₁ hT hG w (TopStep.liftFr_spec d₁.2 w) _ (unitOf_val (hG w))
    have h2 := TopStep.isLiftFr_tilH hN d₂ hT hG w (TopStep.liftFr_spec d₂.2 w) _ (unitOf_val (hG w))
    rw [← H0] at h2
    have e : (TopStep.passFr _ k h1 h2).1 = sumE hN ((d₂.1.liftFr w)⁻¹ * γ'.1 * d₁.1.liftFr w) 1 := by
      rw [← sumE_pass hN _ _ _ (unitOf pi), ← TopStep.extUH_val]
      rfl
    have hi := glint_of_sumE hN (e ▸ (TopStep.passFr _ k h1 h2).2)
    refine ⟨redGL n w.1 ⟨_, hi⟩, ?_⟩
    rw [← TopStep.redGL_extI hN, ← TopStep.redGL_passFr _ k h1 h2]
    exact congrArg _ (Subtype.ext e)
  choose h hh using key
  obtain rfl : k = extGH hN h := funext fun w => (hh w).trans (TopStep.extGH_apply hN h w).symm
  refine ⟨γ', h, rfl, rfl, ?_⟩
  subst hN
  obtain ⟨γ'', e, h'⟩ := DecoSet.til_class_inj hconj hbig hT hG d₁ d₂ _ h H
  obtain rfl : γ' = γ'' := Subtype.ext (sumE_inj rfl (t := 1) (by
    rw [← TopStep.extUH_val, ← TopStep.extUH_val]
    exact congrArg Subtype.val e))
  exact h'

theorem exists_ext_frame (hQ : ∀ P : Q, pi ∉ P.1.asIdeal) (a : UF E N × GLG E N SG × GLQ E N Q) (p q : DecoF E n ∅ SG Q)
    (H : a • tilFr (ST := ST) hN pi p = tilFr (ST := ST) hN pi q) :
    ∃ g : UF E n × GLG E n SG × GLQ E n Q, a = (extUH hN g.1, extGH hN g.2.1, extQ E hN Q g.2.2) ∧ g • p = q := by
  obtain ⟨γ, k, c⟩ := a
  have H1 : (γ, k) • (tilFr (ST := ST) hN pi p).deco = (tilFr (ST := ST) hN pi q).deco := congrArg DecoF.deco H
  rw [tilFr_deco hN hT hG hQ, tilFr_deco hN hT hG hQ] at H1
  obtain ⟨γ', h, rfl, rfl, -⟩ := exists_ext_deco hN hconj hbig hT hG _ _ γ k H1
  have e : ∀ P, (c P).1 = sumE hN ((q.fr P)⁻¹ * γ'.1 * p.fr P) 1 := fun P => by
    have h1 : (extUH hN γ').1 * (tilFr (ST := ST) hN pi p).fr P * ((c P).1)⁻¹ = (tilFr (ST := ST) hN pi q).fr P :=
      congrArg (fun x => DecoF.fr x P) H
    rw [tilFr_fr hN hT hG hQ, tilFr_fr hN hT hG hQ, TopStep.extUH_val, mul_inv_eq_iff_eq_mul] at h1
    rw [← sumE_pass hN _ _ _ (unitOf pi), mul_assoc, h1, inv_mul_cancel_left]
  have hi : ∀ P : Q, (q.fr P)⁻¹ * γ'.1 * p.fr P ∈ GLint E n P.1 := fun P => glint_of_sumE hN (e P ▸ (c P).2)
  obtain rfl : c = extQ E hN Q fun P => ⟨_, hi P⟩ := funext fun P => Subtype.ext (e P)
  refine ⟨(γ', h, _), rfl, tilFr_injective (ST := ST) hN hT hG hQ ?_⟩
  rw [tilFr_smul hN hT hG hQ]
  exact H

end Points

section Size

variable {X : Fields} {Pr : Primes X}

theorem four_lt_level_prime (hPr : Pr.Ok) (u : Pr.Word) : 4 < Pr.T u := by
  set M := Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 with hM
  obtain ⟨z, hz⟩ := hPr.piT_cong u
  have h1 : X.conjO (Pr.piT u) - 1 = (M : 𝓞 X.E) * X.conjO z := by
    have := congrArg X.conjO hz
    rwa [map_sub, map_one, map_mul, map_natCast] at this
  have h2 : ((M : ℤ) : 𝓞 X.E) ∣ (((Pr.T u : ℤ) - 1 : ℤ) : 𝓞 X.E) := by
    refine ⟨z * X.conjO (Pr.piT u) + X.conjO z, ?_⟩
    push_cast
    rw [← hPr.piT_norm u]
    linear_combination X.conjO (Pr.piT u) * hz + h1
  have h3 := map_dvd (Algebra.norm ℤ) h2
  rw [← eq_intCast (algebraMap ℤ (𝓞 X.E)), ← eq_intCast (algebraMap ℤ (𝓞 X.E)), Algebra.norm_algebraMap,
    Algebra.norm_algebraMap, Int.pow_dvd_pow_iff Module.finrank_pos.ne'] at h3
  have hT := (hPr.T_prime u).two_le
  have h4 : ((Pr.g 0 * Pr.g 1) ^ 2 : ℕ) ∣ Pr.T u - 1 := by
    have h5 : M ∣ Pr.T u - 1 := by
      rw [← Int.natCast_dvd_natCast, Nat.cast_sub (by omega)]
      exact h3
    exact (Dvd.intro_left _ hM.symm).trans h5
  have h6 := Nat.le_of_dvd (by omega) h4
  have h7 : 2 * 2 ≤ Pr.g 0 * Pr.g 1 := Nat.mul_le_mul (hPr.g_prime 0).two_le (hPr.g_prime 1).two_le
  have h8 := Nat.pow_le_pow_left h7 2
  omega

theorem two_pow_lt (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    2 ^ Module.finrank ℚ X.E < ∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal := by
  have hf : X.f ≠ 0 := by
    rw [Fields.f, hX.card_Tau]
    exact (Module.finrank_pos).ne'
  rw [hX.rankQ, Finset.prod_congr rfl fun Q hQ => hPr.vT_norm u Q hQ, Finset.prod_const, hPr.vT_card, pow_mul]
  exact Nat.pow_lt_pow_left (four_lt_level_prime hPr u) hf

end Size

section Branch

theorem isBlock_of_mulVec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} (h1 : ∀ x, iniH hN (A'.mulVec x) = A.mulVec (iniH hN x))
    (h2 : ∀ x, A'.mulVec x (Br.iL hN) = x (Br.iL hN)) : BranchFormula.IsBlock hN A' A 1 := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  have hinj : Function.Injective (Br.iC hN) := fun a b h => Fin.ext (congrArg Fin.val h :)
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, hinj.eq_iff]
    rw [e, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, Matrix.mulVec_single_one, Matrix.mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [Matrix.mulVec_single_one, Pi.single_eq_of_ne (hne a).symm] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [Matrix.mulVec_single_one, Pi.single_eq_same] at h
    exact h

theorem brStd_rhoVr {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {N n : ℕ} (hN : N = n + 1) (e : ι → E →+* K)
    {lam : ι → DomWeight N} {sg : ι → DomWeight n} (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) {γ' : GL (Fin N) E} {γ : GL (Fin n) E}
    (h : BranchFormula.IsBlock hN ((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) 1) (G : VV K lam) :
    Br.brStd hN lam sg (rhoVr e lam γ' G) = rhoVr e sg γ (Br.brStd hN lam sg G) := by
  refine BranchFormula.equivariance K ι N n hN lam sg hI hS (invTrK (embGL e γ)) (invTrK (embGL e γ')) (fun τ => ?_) G
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (a b : Fin m), ((invTrK (embGL e g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
      e τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g a b => rfl
  simp only [e1]
  refine ⟨fun a b => by rw [h.1], fun a => ⟨by rw [(h.2.1 a).2, map_zero], by rw [(h.2.1 a).1, map_zero]⟩, by rw [h.2.2, map_one]⟩

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n)

theorem mem_ValC_iff (f : Fr emb σ n → ℂ) :
    f ∈ ValC (Gr emb σ n) lam ↔ ∃ F : VV ℂ lam, fnOf (Gr emb σ n) (shiftOf lam) 1 F.1 = f := by
  have e : ∀ F : VV ℂ lam, evV (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ) F =
      fnOf (Gr emb σ n) (shiftOf lam) 1 F.1 := fun F => by
    rw [evV_apply, MvPolynomial.map_id]
    rfl
  constructor
  · intro hf
    have h : f ∈ Submodule.span ℂ (Set.range (evV (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ))) := by
      rw [span_evV]
      exact hf
    rw [← LinearMap.coe_range, Submodule.span_eq] at h
    obtain ⟨F, rfl⟩ := h
    exact ⟨F, (e F).symm⟩
  · rintro ⟨F, rfl⟩
    rw [← e]
    exact evV_mem_ValC _ _ _ _ F

theorem trFr_fnOf (γ : GL (Fin n) E) (c : Kˣ) (F : VV ℂ lam) :
    trFr emb σ γ c (fnOf (Gr emb σ n) (shiftOf lam) 1 F.1) =
      σ c • fnOf (Gr emb σ n) (shiftOf lam) 1 (rhoVr (embAt σ emb) lam γ F).1 := by
  funext y
  rw [trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  have h := evV_rhoVr_tr (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ) γ F y (frMul emb σ γ⁻¹ y) fun τ =>
    (congrFun (congrArg Subtype.val ((frEquiv emb σ γ).apply_symm_apply y)) τ).symm
  rw [evV_apply, evV_apply, MvPolynomial.map_id, MvPolynomial.map_id] at h
  exact h.symm

theorem polOf_fnOf_one (sh : ι → ℤ) (F : Pol ℂ ι n) :
    polOf (Gr emb σ n) sh (fr0 emb σ n) (fnOf (Gr emb σ n) sh 1 F) = F := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  have h := polOf_fnOf (Gr emb σ n) sh (fr0 emb σ n) F
  rwa [e] at h

end Branch

section Period

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R)

def Saturated : Prop :=
  ∀ (p q : Σ b, Q.S'.D b) (a : (I.S R.m).G Q.b0), a • Q.til p.1 p.2 = Q.til q.1 q.2 →
    ∃ g : Q.S'.G p.1, Q.ext p.1 g = a ∧ (⟨p.1, g • p.2⟩ : Σ b, Q.S'.D b) = q

variable {Q}

end Period

section Levels

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) {N n : ℕ} (hN : N = n + 1)
  {Q : Finset (HeightOneSpectrum (𝓞 X.E))} (hQ : ∀ P : Q, Pr.piT u ∉ P.1.asIdeal)
  {Λ : LevFam X.E X.K N Pr.vGs} {Θ : LevQFam X.E X.K N Q} {Λ' : LevFam X.E X.K n Pr.vGs} {Θ' : LevQFam X.E X.K n Q}
include hX hPr hQ

theorem exists_ext_level (hΛ : ∀ h, extGH hN h ∈ Λ.grp → h ∈ Λ'.grp) (hΘ : ∀ c, extQ X.E hN Q c ∈ Θ.grp → c ∈ Θ'.grp)
    (a : FrmG Λ Θ) (p q : DecoF X.E n ∅ Pr.vGs Q)
    (H : a • tilFr (ST := Pr.vT u) hN (Pr.piT u) p = tilFr (ST := Pr.vT u) hN (Pr.piT u) q) :
    ∃ g : FrmG Λ' Θ', FrmG.incl Λ Θ a = (extUH hN g.1, extGH hN g.2.1.1, extQ X.E hN Q g.2.2.1) ∧ g • p = q := by
  obtain ⟨⟨γ, h, c⟩, e, hg⟩ := exists_ext_frame hN hX.conjE (two_pow_lt hX hPr u) (conj_piT_notMem hPr u)
    (piT_notMem_vGs hPr u) hQ (FrmG.incl Λ Θ a) p q H
  have e1 : a.2.1.1 = extGH hN h := congrArg (fun x => x.2.1) e
  have e2 : a.2.2.1 = extQ X.E hN Q c := congrArg (fun x => x.2.2) e
  exact ⟨(γ, ⟨h, hΛ h (e1 ▸ a.2.1.2)⟩, ⟨c, hΘ c (e2 ▸ a.2.2.2)⟩), e, hg⟩

variable (hΛ : ∀ h, extGH hN h ∈ Λ.grp ↔ h ∈ Λ'.grp) (hΘ : ∀ c, extQ X.E hN Q c ∈ Θ.grp ↔ c ∈ Θ'.grp)
include hΛ hΘ

theorem mem_stabilizer_iff (p : DecoF X.E n ∅ Pr.vGs Q) (a : FrmG Λ Θ) :
    a ∈ MulAction.stabilizer (FrmG Λ Θ) (tilFr (ST := Pr.vT u) hN (Pr.piT u) p) ↔
      ∃ g ∈ MulAction.stabilizer (FrmG Λ' Θ') p,
        FrmG.incl Λ Θ a = (extUH hN g.1, extGH hN g.2.1.1, extQ X.E hN Q g.2.2.1) := by
  constructor
  · intro ha
    obtain ⟨g, e, hg⟩ := exists_ext_level hX hPr u hN hQ (fun h => (hΛ h).1) (fun c => (hΘ c).1) a p p ha
    exact ⟨g, hg, e⟩
  · rintro ⟨g, hg, e⟩
    have h := tilFr_smul (ST := Pr.vT u) hN (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) hQ (FrmG.incl Λ' Θ' g) p
    rw [show FrmG.incl Λ' Θ' g • p = p from hg] at h
    show FrmG.incl Λ Θ a • tilFr (ST := Pr.vT u) hN (Pr.piT u) p = tilFr (ST := Pr.vT u) hN (Pr.piT u) p
    rw [e]
    exact h.symm

end Levels

section Lattices

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

variable (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)
  (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L Tp u i).D b → ℂ)
  (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
  (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u i).D b →
    (stepAt sel mu cst L Tp u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ)

def OverLattices (Q : PerIn (chainAt sel mu cst L Tp u rho rho' cD Th)) : Prop :=
  Q.sg = W.sgW ∧ ∃ h : Q.S' = stepX Ch sel mu P, ∀ p : Σ b, Q.S'.D b,
    (Q.til p.1 p.2).1.1 = tilF sel mu u (h ▸ p : Σ b, (stepX Ch sel mu P).D b).2.1.1

variable {W Ch sel mu cst L P Tp u rho rho' cD Th} {Q : PerIn (chainAt sel mu cst L Tp u rho rho' cD Th)}

end Lattices

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

end Main

section Top

open GlobalTheory.TopStep (TilOk tilTop tilEl topLevG topLevQ topGSD evTop TopDepth inQ)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word}

theorem brC_rho (hW : W.Ok) (γ : UF X.E (R.N R.m - 1)) (x : VV X.K (W.lamTrue u R.m)) :
    brC W u (rhoVr X.emb (W.lamTrue u R.m) (ufGL X.E _ (extUH (N_m_succ R) γ)) x) =
      rhoVr X.emb W.sgTrue (ufGL X.E _ γ) (brC W u x) := by
  have h := brStd_rhoVr (N_m_succ R) X.emb (fun τ => (BranchMembers.members X _ R W hW u τ).1)
    (fun τ => (BranchMembers.members X _ R W hW u τ).2) (γ' := ufGL X.E _ (extUH (N_m_succ R) γ)) (γ := ufGL X.E _ γ) (by
      have e : ∀ y, ((ufGL X.E _ (extUH (N_m_succ R) γ⁻¹) : GL _ _) : Matrix _ _ X.E).mulVec y =
          sumE (N_m_succ R) (γ⁻¹).1 1 y := fun y => by
        rw [← TopStep.extUH_val]
        exact toGLm_mulVec _ y
      rw [← map_inv, ← map_inv, ← map_inv]
      refine isBlock_of_mulVec _ (fun y => ?_) fun y => ?_
      · rw [e]
        exact (TopStep.prH_sumE _ _ _ y).trans (toGLm_mulVec _ _).symm
      · rw [e, TopStep.sumE_last, Units.val_one, one_mul]) x
  rw [brC, Br.brAt, LinearMap.smul_apply, LinearMap.smul_apply, h, map_smul]

end Top

end GlobalTheory.TilClass
