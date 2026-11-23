import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.TilX

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

section ExtL

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1)

theorem extM_mul_incl (g : Matrix (Fin n) (Fin n) A) (M : Matrix (Fin N) (Fin n) A)
    (hM : ∀ b j, M b j = if b = Br.iC hN j then 1 else 0) : extM hN g * M = M * g := by
  subst hN
  ext b j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have e1 : ∑ l, extM rfl g b l * M l j = extM rfl g b (Br.iC rfl j) := by
    rw [Finset.sum_eq_single (Br.iC rfl j)]
    · simp [hM]
    · intro l _ hl
      simp [hM, hl]
    · simp
  rw [e1]
  refine Fin.lastCases ?_ (fun i => ?_) b
  · have h3 : ∀ l : Fin n, Fin.last n ≠ Br.iC (rfl : n + 1 = n + 1) l := fun l => (Fin.castSucc_lt_last l).ne'
    simp only [hM, h3, if_false, zero_mul, Finset.sum_const_zero]
    exact extM_last_castSucc g j
  · have h3 : ∀ l : Fin n, (i.castSucc = Br.iC (rfl : n + 1 = n + 1) l) ↔ i = l := fun l => Fin.castSucc_inj
    simp only [hM, h3]
    simp
    exact extM_castSucc g i j

theorem extM_mulVec_fix (g : Matrix (Fin n) (Fin n) A) (z : Fin N → A) (hz : ∀ b, b ≠ Br.iL hN → z b = 0) :
    extM hN g *ᵥ z = z := by
  funext b
  by_cases e : b = Br.iL hN
  · subst e
    rw [extM_mulVec_iL]
  · have hb : b.1 < n := by
      have h3 := b.2
      have h4 : b.1 ≠ n := fun h => e (Fin.ext h)
      omega
    have e2 : b = Br.iC hN ⟨b.1, hb⟩ := Fin.ext rfl
    rw [e2, extM_mulVec_iC]
    have : iniH hN z = 0 := by
      funext i
      refine hz _ fun h => ?_
      have := congrArg Fin.val h
      exact absurd this (Nat.ne_of_lt i.2)
    rw [this, Matrix.mulVec_zero]
    exact (hz _ (by rw [← e2]; exact e)).symm

theorem eq_extM_of_laws (g : Matrix (Fin n) (Fin n) A) (G : Matrix (Fin N) (Fin N) A)
    (h1 : ∀ x, iniH hN (G *ᵥ x) = g *ᵥ iniH hN x) (h2 : ∀ x, (G *ᵥ x) (Br.iL hN) = x (Br.iL hN)) : G = extM hN g := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  funext b
  by_cases e : b = Br.iL hN
  · subst e
    rw [h2, extM_mulVec_iL]
  · have hb : b.1 < n := by
      have h3 := b.2
      have h4 : b.1 ≠ n := fun h => e (Fin.ext h)
      omega
    have e2 : b = Br.iC hN ⟨b.1, hb⟩ := Fin.ext rfl
    rw [e2, extM_mulVec_iC]
    exact congrFun (h1 _) _

end ExtL
set_option maxHeartbeats 1600000 in
theorem exists_ka_tw (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Ch → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k) (c : (I.stX a).Cl) {y' : GA B (B.R.N B.R.m - 1)}
    (hp : PtOf (extGL (N_m_succ B.R) y' * k (chOf ((I.perIn u a).tilC c)))
      (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1)) :
    ∃ κ : U (chOf ((I.perIn u a).tilC c)),
      bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))) *
          y ((I.perIn u a).tilC c) = extGL (N_m_succ B.R) y' * κ.1 ∧
      (((chi _ κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a B.R.m).chr _
        ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) : B.LLˣ) : B.LL) := by
  have hm := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm ⊢
  have hp' : PtOf (ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (extGL (N_m_succ B.R) y' * k (chOf ((I.perIn u a).tilC c)))) _ := isPtOf_rat hp (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹
  let κ0 : (I.stp u a B.R.m).G (I.perIn u a).b0 := (1, m.2.1, m.2.2)
  have hgam : (I.stp u a B.R.m).gam (I.perIn u a).b0 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m))
  have hempty : ∀ p : (I.stp u a B.R.m).D (I.perIn u a).b0, p.1.2 = ∅ := fun p => by
    have h := p.2
    rw [congrArg (fun y => y.ys p.1.1.deco.1.N) (ysAt_m B.R I.sel (I.tup a) (I.cst a))] at h
    exact h
  have hact : ((I.stp u a B.R.m).act (I.perIn u a).b0 κ0 ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 =
      (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) •
        (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1) := by
    have e1 : FrmG.incl _ _ m • ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1 =
        tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1 :=
      congrArg (fun d : (I.stp u a B.R.m).D (I.perIn u a).b0 => d.1.1) hm
    rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m (I.perIn u a).b0)
        (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m (I.perIn u a).b0) κ0 =
        (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) *
        FrmG.incl _ _ m := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun t => t • ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1) e2
  have hcos : cosetIn ((I.stp u a B.R.m).act (I.perIn u a).b0 κ0 ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))) =
      cosetIn ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)) := by
    ext z
    simp [cosetIn, hempty]
  obtain ⟨x, hx⟩ : ∃ x : GA B (B.R.N B.R.m), x = (y ((I.perIn u a).tilC c))⁻¹ * ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * extGL (N_m_succ B.R) y' := ⟨_, rfl⟩
  have hxk : y ((I.perIn u a).tilC c) * x * k (chOf ((I.perIn u a).tilC c)) = ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (extGL (N_m_succ B.R) y' * k (chOf ((I.perIn u a).tilC c))) := by
    rw [hx]; group
  have hq : PtOf (y ((I.perIn u a).tilC c) * x * k (chOf ((I.perIn u a).tilC c))) ((I.stp u a B.R.m).act (I.perIn u a).b0 κ0 ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 := by
    rw [hxk, hact]
    exact hp'
  have hxU : x ∈ U (chOf ((I.perIn u a).tilC c)) := (hR.lev ((I.perIn u a).tilC c) x _ hq).2 ⟨κ0, hgam, rfl, hcos⟩
  have hchr := hR.chr ((I.perIn u a).tilC c) ⟨x, hxU⟩ κ0 hgam hq
  refine ⟨⟨x, hxU⟩⁻¹, ?_, ?_⟩
  · have e : ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a B.R.m).gam (I.perIn u a).b0 m))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    show _ = extGL (N_m_succ B.R) y' * x⁻¹
    rw [hx, e]
    group
  · rw [map_inv, inv_inv]
    exact hchr

theorem til_lat_eq_tw (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (hiX : ∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) (u : B.Word) (a : I.ι) (c : (I.stX a).Cl) :
    Formalism.L2.Forms.mulLat (((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) : GL _ _) : Matrix _ _ _)
      ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1.deco.1.L =
    (((I.stX a).rep c).1.1.deco.1.N).map ((iXc (I.rec7 l Z)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) ⊔
      Submodule.span (𝓞 (I.rec7 l Z).host.E) {z0v B X u} := by
  have hPr := (base_fields_primes_ok B X).2.1
  have hm := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm ⊢
  have e0 : ((I.perIn u a).tilPt c).1.1.deco = DecoSet.tilH (N_m_succ B.R) ((B.primes X).piT u) ((I.stX a).rep c).1.1.deco :=
    PerLaw.til_deco hI u a _ _
  have e1 : ((I.perIn u a).tilPt c).1.1.deco.1 =
      ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1.deco.1.act m.1.1 m.2.1.1 := by
    have := congrArg (fun d : (I.stp u a B.R.m).D (I.perIn u a).b0 => d.1.1.deco.1) hm
    exact this.symm
  have e2 := L_act ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1.deco.2 m.1.2 m.2.1.1
  rw [← e1, e0, til_L_eq (N_m_succ B.R) (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) (fun P => decoFin_mem_of_mem_divs P.2)
    (piT_dvd_of_mem (base_fields_primes_ok B X).1 hPr u) _ (iXc (I.rec7 l Z)) hiX (z0v B X u) (fun j => rfl)] at e2
  exact (mulLat_toGLm m.1.1 _).trans e2.symm

set_option maxHeartbeats 1600000 in
theorem til_fv_eq_tw (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (hg : gramN (I.rec7 l Z) B.R.m le_rfl = 1) (u : B.Word) (a : I.ι)
    {lat : (I.stp u a B.R.m).Cl → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    (hsu : ∀ c, lat c = ((I.stp u a B.R.m).rep c).1.1.deco.1.L)
    {res : ∀ v : (I.atT l u a).vT, 𝓞 B.host.E →+* (I.atT l u a).Fv v}
    (L : LevelCompatibleLattices (D := I.rec7 l Z) (I.fm l u a) (B.T u) res B.R.m le_rfl lat) (hres : res = I.resT l u a)
    (hL : ∀ v c (z : LdG (I.rec7 l Z) B.R.m le_rfl (lat c)) (h : z.1 ∈ ((I.stp u a B.R.m).rep c).1.1.deco.1.N),
      L.pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩)
    (v : (I.atT l u a).vT) (c : (I.stX a).Cl) (x : ↥(LdG (I.rec7 l Z) B.R.m le_rfl (lat ((I.fm l u a).til c))))
    (r : 𝓞 (I.rec7 l Z).host.E)
    (hr : (r : (I.rec7 l Z).host.E) = hform (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl) (z0v B X u)
      (((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))).1 *ᵥ x.1)) :
    (I.fm l u a).fv B.R.m v ((I.fm l u a).til c) (L.pr v _ x) = res v r := by
  have hPr := (base_fields_primes_ok B X).2.1
  have hm := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm hr
  have hx1 : x.1 ∈ ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1.deco.1.Lsh := by
    have h1 := x.2
    have h2 : x.1 ∈ dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl)
      (lat ((I.fm l u a).til c)) := h1
    rw [hg] at h2
    have h3 := Eq.mp (congrArg (fun M => x.1 ∈ dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) 1 M)
      (hsu ((I.fm l u a).til c))) h2
    exact dualL_le_Lsh (E := B.host.E) _ (fun _ => rfl) _ h3
  obtain ⟨xv, hxv⟩ : ∃ xv : Sp B.fields.E (B.R.N B.R.m), xv = x.1 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 B.fields.E, s = cO B.fields.E ((B.primes X).piT u) := ⟨_, rfl⟩
  have hsN : s • xv ∈ ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1.deco.1.N := by
    refine ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)).1.1.deco.2.smul_Lsh_mem_N (fun P => ?_) (hxv ▸ hx1)
    rw [hs, cO_cO]
    exact decoFin_mem_of_mem_divs P.2
  have h0 : ((show 𝓞 (I.rec7 l Z).host.E from s) • x).1 = s • xv := by rw [hxv]; rfl
  have h1 := hL v _ ((show 𝓞 (I.rec7 l Z).host.E from s) • x) (h0 ▸ hsN)
  have h2 := L.pr_smul v _ (show 𝓞 (I.rec7 l Z).host.E from s) x
  have hne := ((l.fmL u a).lev B.R.m).fv_ne v ((I.perIn u a).tilC c)
  have h3 := TDat.fv_mk ((I.atIn u a).A B.R.m) v ((I.perIn u a).tilC c) hne ⟨s • xv, hsN⟩
  have hlev := (l.lev u a).lev B.R.m
  have h4 := hlev.f_act (I.perIn u a).b0 m ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)) v (s • xv)
  have h5 := (hlev.N_act (I.perIn u a).b0 m ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)) (s • xv)).2 hsN
  have h4' := congrArg (fun d => ((I.atIn u a).A B.R.m).f (I.perIn u a).b0 d v
    (((I.stp u a B.R.m).gam (I.perIn u a).b0 m).1 *ᵥ (s • xv))) hm
  have h5' := Eq.mp (congrArg (fun d => ((I.stp u a B.R.m).gam (I.perIn u a).b0 m).1 *ᵥ (s • xv) ∈
    ((I.atIn u a).A B.R.m).N (I.perIn u a).b0 d) hm) h5
  have h6 := (l.ovr u a).f_til c.1 ((I.stX a).rep c) v _ h5'
  obtain ⟨rv, hrv⟩ : ∃ rv : 𝓞 B.fields.E, rv = r := ⟨_, rfl⟩
  have hr' : algebraMap (𝓞 B.fields.E) B.fields.E rv = star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) *
      (((I.stp u a B.R.m).gam (I.perIn u a).b0 m).1 *ᵥ xv) (Br.iL (N_m_succ B.R)) := by
    rw [hg, lastCoordinateUniformizerVector_eq_single] at hr
    rw [hrv, hxv]
    refine hr.trans ((hform_one_single (A := B.host.E) (ι := Fin (B.R.N B.R.m)) _ (Br.iL (N_m_succ B.R)) _ _).trans ?_)
    rfl
  have h7 : ((I.perIn u a).tz * (((I.stp u a B.R.m).gam (I.perIn u a).b0 m).1 *ᵥ (s • xv)) (Br.iL (N_m_succ B.R))) =
      algebraMap (𝓞 B.fields.E) B.fields.E (s * rv) := by
    have e1 : (((I.stp u a B.R.m).gam (I.perIn u a).b0 m).1 *ᵥ (s • xv)) (Br.iL (N_m_succ B.R)) =
        algebraMap (𝓞 B.fields.E) B.fields.E s * (((I.stp u a B.R.m).gam (I.perIn u a).b0 m).1 *ᵥ xv) (Br.iL (N_m_succ B.R)) := by
      rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
    rw [e1, map_mul, hr']
    show star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) * _ = _
    ring
  have h8 : ((I.atIn u a).A B.R.m).f (I.perIn u a).b0 ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)) v (s • xv) =
      Ideal.Quotient.mk v.1.asIdeal (s * rv) := by
    refine h4.symm.trans (h4'.trans (h6.trans ?_))
    rw [h7]
    exact reduction_coe _ _
  have hresv : res v = Ideal.Quotient.mk v.1.asIdeal := congrFun hres v
  subst hxv hrv
  have hs0 : Ideal.Quotient.mk v.1.asIdeal s ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, hs]
    exact conj_piT_notMem hPr u v
  obtain ⟨pv, hpv⟩ : ∃ pv : ((I.atIn u a).A B.R.m).lv v ((I.perIn u a).tilC c), pv = L.pr v _ x := ⟨_, rfl⟩
  have h2' : (L.pr v _ ((show 𝓞 (I.rec7 l Z).host.E from s) • x) : ((I.atIn u a).A B.R.m).lv v ((I.perIn u a).tilC c)) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) • pv := by
    rw [hpv]
    have h2a := h2
    rw [hresv] at h2a
    exact h2a
  have h9 : ((I.atIn u a).A B.R.m).fv v ((I.perIn u a).tilC c) ((Ideal.Quotient.mk v.1.asIdeal s : Res v.1) • pv) =
      Ideal.Quotient.mk v.1.asIdeal (s * rv) := by
    exact (congrArg (fun w => ((I.atIn u a).A B.R.m).fv v ((I.perIn u a).tilC c) w) (h2'.symm.trans h1)).trans (h3.trans h8)
  rw [map_smul, smul_eq_mul, map_mul] at h9
  rw [hresv, ← hpv]
  exact mul_left_cancel₀ (M₀ := Res v.1) hs0 h9

set_option maxHeartbeats 4000000 in

theorem til_tw (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {l0 : I.Law0 l} {inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)}
    {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)} {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {J : Formalism.L2.Herm.TwChJointS T H}
    {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W}
    (hF : ∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) (hW : I.StdW l Z l0 W) (hLv : I.StdLv l Z l0 Lv)
    (u : B.Word) (a : I.ι) (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m)
    (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) (T.Q a)))
    (hK : I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat fun c s => (K.stabI c s).1)
    {k : T.Ch u a B.R.m → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k)
    (hT : ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) :
    ∃ Tl : SymmetricTwistedTiltedData Lv u a ha h1 K, Tl.z0 = TC.z0 X u ∧
      ∀ (φ : (I.chain l u a).cls B.R.m → (I.chain l u a).Y B.R.m → ℂ) c s s',
        IsTr (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Tl.ga c).1.1) (twYS T F u a B.R.m le_rfl s') (twYS T F u a B.R.m le_rfl s) →
        (I.per l u a).evz φ c s =
          ((((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m ((I.fm l u a).til c))).lev.chi (Tl.ka c))⁻¹ : ℂˣ) : ℂ) *
            φ ((I.fm l u a).til c) s' := by
  obtain ⟨-, -, hiX, hsp⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  obtain ⟨hg, -, hsu⟩ := hsp B.R.m le_rfl
  have hcls := (hsu u a).1
  have hN := N_m_succ B.R
  have hPr := (base_fields_primes_ok B X).2.1
  have hga : ∀ c, (I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) ∈
      UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl) := by
    intro c
    rw [hg]
    show cT _ _ * 1 * _ = 1
    rw [mul_one]
    exact ((l.ch u a).step B.R.m).unit _ _
  have hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
    intro h0
    have h1 : X.piT u = 0 := RingOfIntegers.ext h0
    have h2 := hPr.piT_norm u
    have h3 : (B.primes X).piT u = 0 := h1
    rw [h3, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  have hext : ∀ (R' : Type) [CommRing R'] (φ : (I.rec7 l Z).host.E →+* R') (g' : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) R'),
      IsExt (I.rec7 l Z) (z0 X u) φ g' (extM hN g') := by
    intro R' _ φ g'
    refine ⟨extM_mul_incl hN g' _ fun b j => ?_, extM_mulVec_fix hN g' _ fun b hb => ?_⟩
    · refine (congrArg φ (TilX.iXm_apply hiX hN b j)).trans ?_
      by_cases h : b = Br.iC hN j
      · rw [if_pos h]
        exact (congrArg φ (if_pos h)).trans φ.map_one
      · rw [if_neg h]
        exact (congrArg φ (if_neg h)).trans φ.map_zero
    · show φ (TC.z0 X u b) = 0
      have e : TC.z0 X u = z0v B X u := rfl
      rw [e, lastCoordinateUniformizerVector_eq_single, Pi.single_eq_of_ne hb]
      exact φ.map_zero
  have hka := fun c => exists_ka_tw I u a hR c (y' := (K.y c).1)
    (hT _ _ _ _ (hK.pt c) (hext _ _ _))
  choose ka hka1 hka2 using hka
  have hsu' : ∀ c, latCrd (I.rec7 l Z) B.R.m le_rfl (T.lat u a B.R.m c) = ((I.stp u a B.R.m).rep c).1.1.deco.1.L := fun c => by
    rw [hW.lat u a B.R.m]
    exact hcls c
  have hres : (W.atT u a).res (F u).atT = I.resT l u a := funext fun v => RingHom.ext (hW.eFv u a v)
  have hgamX : ∀ c (s : (I.stX a).Stab c), (((I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).ext c.1 s.1) : GL _ _) : Matrix _ _ _) =
      extM hN (((I.stX a).gam c.1 s.1 : GL _ _) : Matrix _ _ _) := fun c s =>
    eq_extM_of_laws hN _ _ (fun x => (l.per u a).gam_ini c.1 s.1 x) (fun x => (l.per u a).gam_last c.1 s.1 x)
  let Tl : SymmetricTwistedTiltedData Lv u a ha h1 K :=
    { z0 := z0v B X u
      lastCoordinateUniformizerVector_spans_orthogonal_line := TilX.lastCoordinateUniformizerVector_spans_orthogonal_line I l Z hg hiX u
      hermitianForm_lastCoordinateUniformizerVector_self := TilX.hermitianForm_lastCoordinateUniformizerVector_self I l Z hg u
      ga := fun c => ⟨_, hga c⟩
      til_lat := fun c => (congrArg (Formalism.L2.Forms.mulLat _) (hsu' ((I.perIn u a).tilC c))).trans
          ((til_lat_eq_tw I hI l Z hiX u a c).trans (by rw [hK.lat c]; rfl))
      til_fv := fun v c x r hr => (til_fv_eq_tw I hI l Z hg u a hsu' (Lv.lv u a ha B.R.m h1 le_rfl) hres
        (hLv u a ha B.R.m h1 le_rfl).1 v c x r hr)
      stabMap := fun c s => by
        have e1 := hK.stab c s
        have e2 := hR.stab ((I.perIn u a).tilC c) ((I.perIn u a).stabMap (l.per u a) c s)
        have e3 : ((I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).stabMap (l.per u a) c s).1 : GL _ _) =
            ((I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ *
              (I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).ext c.1 s.1) *
              (I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) := by
          show (I.stp u a B.R.m).gam (I.perIn u a).b0 (((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))⁻¹ *
            (I.perIn u a).ext c.1 s.1 * (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) = _
          rw [_root_.map_mul, _root_.map_mul, _root_.map_inv]
        have e4 : ∀ (A M : GL (Fin (B.R.N B.R.m)) B.host.E), A.1 * (A⁻¹ * M * A).1 * (A⁻¹).1 = M.1 := by
          intro A M
          rw [← Units.val_mul, ← Units.val_mul]
          congr 1
          group
        have e5 := hext B.host.E (RingHom.id _) ((I.stX a).gam c.1 s.1).1
        have e6 := hgamX c s
        have e7 : ((K.stabI c s).1).1 = ((I.stX a).gam c.1 s.1).1 := congrArg Units.val e1
        have e8 := congrArg (fun M : GL (Fin (B.R.N B.R.m)) B.host.E =>
          ((I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))).1 * M.1 *
            (((I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹).1) (e2.trans e3)
        exact Eq.mpr (congrArg₂ (fun p q => IsExt (I.rec7 l Z) (z0v B X u) (RingHom.id _) p q) e7 (e8.trans ((e4 _ _).trans e6))) e5
      ka := ka
      til_ad := fun c g hg' => by
        have e : g.1 = extM hN (K.y c).1.1 := by
          refine TilX.eq_extM_of_ext hN (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) hpi0
            (TilX.iXm_apply hiX hN) hg'.1 ?_
          have h2 := hg'.2
          rw [show (z0v B X u) = _ from lastCoordinateUniformizerVector_eq_single u] at h2
          exact h2
        have e' : g = extGL hN (K.y c).1 := Units.ext e
        rw [e']
        exact hka1 c }
  refine ⟨Tl, rfl, ?_⟩
  intro φ c s s' hs
  have hyS : ∀ s, (twYS T F u a B.R.m le_rfl s).1 = s.1 := fun s => by
    have e := congrArg (fun f => Equiv.symm f s) (hW.eY u a B.R.m le_rfl)
    refine (congrArg (fun y => (eYS (F u) B.R.m le_rfl y).1) e).trans ?_
    show (eYS (F u) B.R.m le_rfl s).1 = s.1
    rw [eYS_end (F u) B.R.m le_rfl (Or.inr rfl)]
    exact (hF u).1.eY _ _ (Or.inr rfl) s
  have hy1 := hyS s
  have hy2 := hyS s'
  have hemb : ∀ τ, Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Tl.ga c).1.1 τ =
      (((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))).1).map (embAt B.embLL B.fields.emb τ) := fun τ =>
    congrArg (fun f : B.host.E →+* ℂ => ((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))).1.map f) (B.fields_embC τ).symm
  have e1 := TilX.frMul_inv_eq B.fields.emb B.embLL ((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))) s s'
    (fun τ => (congrFun hy1 τ).symm.trans ((hs τ).trans (congrArg₂ (· * ·) (hemb τ) (congrFun hy2 τ))))
  have e2 := trFr_apply B.fields.emb B.embLL ((I.stp u a B.R.m).gam _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))
    ((I.stp u a B.R.m).chr _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))) (φ ((I.perIn u a).tilC c)) s
  rw [e1, ← hka2 c] at e2
  exact e2

end GlobalTheory.Mem.Col2.TwP

end
