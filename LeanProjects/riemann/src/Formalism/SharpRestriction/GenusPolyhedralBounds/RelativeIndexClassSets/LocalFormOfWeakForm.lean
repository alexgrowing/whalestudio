import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ConclOfHyp

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    0 ≤ X.phiC la y := by
  unfold PJ.phiC
  split_ifs with h
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    unfold ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC
    refine Real.sInf_nonneg ?_
    rintro x ⟨l, -, h2, rfl⟩
    by_cases hb : (P.loc X.dat (resCh la)).beS (X.pt66 la y) = 0
    · rw [hb]; simp
    · refine (h2 _ ?_ hb).le
      intro a
      by_cases ha : a = 0
      · subst ha; simp
      · exact ((P.loc X.dat (resCh la)).be_pos (X.pt66 la y) a ha).le
  · exact le_rfl

abbrev trivDat (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (ϖ : X.Ol la) : LocDat X ka la where
  O' := X.Ol la
  K' := X.Kl la
  V₁ := ↥(WL X ka la)
  bc := LinearMap.id
  ϖ := ϖ
  K₁ := X.Kl la
  ι := Empty
  y := Empty.elim
  ν := Empty.elim
  ep := Empty.elim
  f := Empty.elim
  R := 0
  I := 0
  N₁ := ⊥
  Z := ThW X S ka wL wF T la
  Zm := MW X ka la
  N' := MW X ka la
  n := 0
  be := 0
  th := Fin.elim0
  c := 0
  Wsec := PUnit
  AA := ⊥
  AA' := ⊥
  N₁' := ⊥
  ρ := 0
  a := 1
  a' := 1
  Rr := fun _ => X.Ol la
  Aq := fun _ => X.Ol la
  hR := fun z => z.elim
  xq := fun _ => 0
  nq := fun _ => 0
  Fq := fun _ _ => ⊥
  rq := fun _ _ => 0
  A0 := PUnit
  n1 := 0
  F1 := fun _ => ⊤
  ι1 := Empty
  deg := Empty.elim
  δ := 0
  t := Fin.elim0
  σ := fun _ => 0
  u := Empty.elim

theorem up_trivDat (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (ϖ : X.Ol la) (N : Submodule (X.Ol la) ↥(WL X ka la)) :
    (trivDat X S ka wL wF T la ϖ).up N = N := by
  rw [LocDat.up]
  have himg : ((trivDat X S ka wL wF T la ϖ).bc '' (N : Set ↥(WL X ka la))) = (N : Set ↥(WL X ka la)) :=
    Set.image_id _
  rw [himg]
  exact Submodule.span_eq N

theorem subsingleton_quot {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M]
    (N : Submodule R M) : Subsingleton (M ⧸ N) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N a
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N b
  rw [Subsingleton.elim x y]

theorem triv_ok (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T e : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (ϖ : X.Ol la) (hϖ : Irreducible ϖ)
    (hL : InLat X ka la S wL wF T) (hle : ThW X S ka wL wF T la ≤ MW X ka la) :
    (trivDat X S ka wL wF T la ϖ).Ok S wL wF T e := by
  refine ⟨hL, ⟨?_, hϖ, hϖ⟩, fun z => z.elim, ?_, ?_, ?_⟩
  · exact IsBaseChange.ofEquiv (LinearEquiv.refl (X.Kl la) ↥(WL X ka la))
  · unfold LocDat.InRes
    rw [up_trivDat, up_trivDat]
    dsimp (config := {instances := true}) only [trivDat]
    have hspan : Submodule.span (X.Kl la)
        (((⊥ : Submodule (X.Ol la) ↥(WL X ka la)) ⊔ ThW X S ka wL wF T la :
          Submodule (X.Ol la) ↥(WL X ka la)) : Set ↥(WL X ka la)) = ⊤ := by
      rw [bot_sup_eq]; exact hL.2.2
    refine ⟨?_, fun i => i.elim0, fun i => i.elim0, ?_, ?_, fun _ _ i => i.elim0, one_ne_zero,
      one_ne_zero, ?_, ?_, bot_le, hle, le_rfl, ?_, ?_, ?_, le_rfl, le_rfl, ?_⟩
    · rw [bot_sup_eq]
    · rw [hspan]; exact le_top
    · rw [LinearMap.ker_zero, top_sup_eq]
    · simp
    · refine inf_le_left.trans ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (MW X ka la).smul_mem _ hx
    · intro x; simp
    · rw [LinearMap.ker_zero]; simp
    · exact Subsingleton.elim _ _
    · exact Formalism.LatticeIndexTer.latFinite _ (X.Kl la) _ _ _ hL.1 hL.2
  · refine ⟨fun z => z.elim, fun z => z.elim, fun z => z.elim, fun z => z.elim, fun z => z.elim,
      fun z => z.elim, fun z => z.elim, ?_⟩
    dsimp (config := {instances := true}) only [trivDat]
    have := subsingleton_quot
      ((⊥ : Submodule (X.Ol la) PUnit).comap (⊥ : Submodule (X.Ol la) PUnit).subtype)
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · unfold LocDat.InLead
    dsimp (config := {instances := true}) only [trivDat]
    refine ⟨rfl, Subsingleton.elim _ _, fun _ => le_rfl, fun _ => Subsingleton.elim _ _,
      fun _ y => ⟨0, Subsingleton.elim _ _⟩, fun α => α.elim, fun α => α.elim,
      linearIndependent_empty_type, Subsingleton.elim _ _, rfl, ?_⟩
    rw [Nat.cast_zero, Module.length_eq_zero_iff]
    exact subsingleton_quot _

theorem triv_err (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (ϖ : X.Ol la) (c : ℝ) :
    (trivDat X S ka wL wF T la ϖ).err T c =
      ((Module.length (X.Ol la)
        (↥(MW X ka la) ⧸ (ThW X S ka wL wF T la).comap (MW X ka la).subtype)).toNat : ℝ) := by
  simp [LocDat.err, trivDat]

theorem exists_ok_err (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T e : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (hL : InLat X ka la S wL wF T)
    (hle : ThW X S ka wL wF T la ≤ MW X ka la) :
    ∃ L : LocDat X ka la, L.Ok S wL wF T e ∧ ∀ c : ℝ, L.err T c =
      ((Module.length (X.Ol la)
        (↥(MW X ka la) ⧸ (ThW X S ka wL wF T la).comap (MW X ka la).subtype)).toNat : ℝ) := by

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.Ol la)
  exact ⟨trivDat X S ka wL wF T la ϖ, triv_ok X S ka wL wF T e la ϖ hϖ hL hle,
    fun c => triv_err X S ka wL wF T la ϖ c⟩

namespace LocDat

variable {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {la : HeightOneSpectrum (𝓞 B.KO)} (L : LocDat X ka la)

def InTieW (S : Scal B) (wL : WeightFamilies.Wt D j) : Prop :=
  ∀ z, ((L.ν z : ℝ) : EReal) ≤ X.depth S.sW wL la (L.y z) ∧ (∃ m : ℤ, (L.ep z : ℝ) * L.ν z = m) ∧
    1 ≤ L.ep z

def OkW (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T e : ℕ) : Prop :=
  InLat X ka la S wL wF T ∧ L.InExt ∧ L.InTieW S wL ∧ L.InRes S wL wF T e ∧ L.InPts T e ∧ L.InLead

variable {L}

theorem InTie.toW {S : Scal B} {wL : WeightFamilies.Wt D j} (h : L.InTie S wL) : L.InTieW S wL := by
  intro z
  obtain ⟨h1, h2, h3, -⟩ := h z
  exact ⟨h1.symm.le, h2, h3⟩

theorem Ok.toW {S : Scal B} {wL wF : WeightFamilies.Wt D j} {T e : ℕ} (h : L.Ok S wL wF T e) :
    L.OkW S wL wF T e := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact (show _ ∧ _ ∧ _ ∧ _ from ⟨h1, h2, InTie.toW h3, h4⟩)

end LocDat

theorem idx_bound_of_le (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (e : ℕ) (nu c : ℝ) (hT : 1 ≤ T) (hc : 0 ≤ c)
    (hTe : (T : ℝ) * nu ≤ (e : ℝ)) (L : LocDat X ka la) (hLat : InLat X ka la S wL wF T)
    (hExt : L.InExt) (hν : ∀ z, L.ν z ≤ nu + c * L.v z)
    (hint : ∀ z, ∃ m : ℤ, (L.ep z : ℝ) * L.ν z = m) (hep : ∀ z, 1 ≤ L.ep z)
    (hRes : L.InRes S wL wF T e) (hPts : L.InPts T e) (hLead : L.InLead)
    (U : Submodule (X.Kl la) ↥(WL X ka la)) :
    (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(WL X ka la) (MW X ka la ⊓ U.restrictScalars (X.Ol la))
              (ThW X S ka wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤
      (e : ℝ) * (finrank (X.Kl la) U : ℝ) + L.err T c := by
  obtain ⟨hMlat, hΘlat⟩ := hLat
  obtain ⟨hbc, hϖ, hϖ'⟩ := hExt
  have : FiniteDimensional (X.Kl la) ↥(WL X ka la) := finDim_of_isLat _ hMlat
  have hM₁ := Formalism.LatticeBaseChangeAlt.isLattice_span_image_alt (X.Ol la) L.O' (X.Kl la) L.K' ↥(WL X ka la) L.V₁ L.bc hbc _ hMlat
  have hΘ₁ := Formalism.LatticeBaseChangeAlt.isLattice_span_image_alt (X.Ol la) L.O' (X.Kl la) L.K' ↥(WL X ka la) L.V₁ L.bc hbc _ hΘlat
  have : FiniteDimensional L.K' L.V₁ := finDim_of_isLat _ hM₁
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19⟩ := hRes
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hPts
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLead
  have key := Formalism.LatticeBaseChangeAlt.localStepClosed L.ι L.ep L.f L.ν L.v nu c T L.R L.I
    hep hT hc (fun z => phiC_nonneg X la (L.y z)) hν L.O' L.K' L.K₁ L.V₁ L.Wsec
    (algebraMap (X.Ol la) L.O' L.ϖ) hϖ' (L.up (MW X ka la)) (L.up (ThW X S ka wL wF T la)) L.N₁ L.Z L.Zm L.N'
    e L.be L.n L.th L.c L.AA L.AA' L.N₁' L.ρ L.a L.a' hM₁ hΘ₁
    r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
    (Or.inl ⟨hTe, hint⟩) L.Rr L.Aq L.xq L.nq L.Fq L.rq p1 p2 p3 p4 p5 p6 p7 p8
    L.A0 L.n1 L.F1 L.ι1 L.deg L.δ L.t L.σ L.u l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
    (Submodule.span L.K' (L.bc '' (U : Set ↥(WL X ka la))))
  have hd : (0 : ℝ) < (finrank L.K' L.K₁ : ℝ) := by exact_mod_cast (finrank_pos : 0 < finrank L.K' L.K₁)
  have desc := Formalism.LatticeBaseChangeAlt.localStepDescent (X.Ol la) L.O' (X.Kl la) L.K' ↥(WL X ka la) L.V₁ L.bc hbc L.ϖ hϖ hϖ'
    (MW X ka la) (ThW X S ka wL wF T la) U hMlat hΘlat (finrank L.K' L.K₁ : ℝ)
    ((L.R : ℝ) * ((T : ℝ) * c * ∑ z, ((L.ep z : ℝ) * L.f z) * L.v z) +
      (L.R : ℝ) * (L.I : ℝ) + ((Module.length L.O' (↥L.Zm ⧸ L.Z.comap L.Zm.subtype)).toNat : ℝ))
    (((IsDiscreteValuationRing.addVal L.O' L.a).toNat : ℝ) -
        ((IsDiscreteValuationRing.addVal L.O' L.a').toNat : ℝ) +
        (finrank L.K' L.K₁ : ℝ) * (L.n : ℝ) * (L.be : ℝ)) e
    (by
      refine le_trans key (le_of_eq ?_)
      ring)
  unfold LocDat.err
  rw [← mul_le_mul_iff_right₀ hd]
  refine le_trans desc (le_of_eq ?_)
  field_simp
  ring

theorem nu_le_of_tieW (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (ka wL : WeightFamilies.Wt D j)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO))
    (hH1 : H1 large₂ X H S wL nus) (L : LocDat X ka la) (hTie : L.InTieW S wL) (z : L.ι) :
    L.ν z ≤ nus la + max 0 (cc D large₂ H.Cc H.Ac H.CRc wL) * L.v z := by
  have h : L.ν z ≤ nus la + cc D large₂ H.Cc H.Ac H.CRc wL * X.phiC la (L.y z) :=
    EReal.coe_le_coe_iff.1 ((hTie z).1.trans (hH1.2.2.2 la (L.y z)))
  have hv : 0 ≤ X.phiC la (L.y z) := phiC_nonneg X la (L.y z)
  have hm : cc D large₂ H.Cc H.Ac H.CRc wL * X.phiC la (L.y z) ≤
      max 0 (cc D large₂ H.Cc H.Ac H.CRc wL) * X.phiC la (L.y z) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hv
  show L.ν z ≤ nus la + max 0 (cc D large₂ H.Cc H.Ac H.CRc wL) * X.phiC la (L.y z)
  linarith

def Thm0LocalW : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) (e : ℕ),
    H1 large₂ X H S wL nus → 1 ≤ T →
    X.Theta S ka wL wF T ≤ X.Msup ka →
    (T : ℝ) * nus la ≤ (e : ℝ) →
    ∀ L : LocDat X ka la, L.OkW S wL wF T e →
    ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
      X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
          (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
          (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
        (e : ℝ) * (finrank (X.Kl la) V' : ℝ) + L.err T (max 0 (cc D large₂ H.Cc H.Ac H.CRc wL))

theorem thm0LocalW : @Thm0LocalW D B P j := by
  intro large₂ X H S ka wL wF T nus la e hH1 hT hΘM hTe L hOk V' hV'
  obtain ⟨hLat, hExt, hTie, hRes, hPts, hLead⟩ := hOk
  have hb := idx_bound_of_le X S ka wL wF T la e (nus la) (max 0 (cc D large₂ H.Cc H.Ac H.CRc wL)) hT
    (le_max_left _ _) hTe L hLat hExt (nu_le_of_tieW large₂ X H S ka wL nus la hH1 L hTie)
    (fun z => (hTie z).2.1) (fun z => (hTie z).2.2) hRes hPts hLead (V'.comap (WL X ka la).subtype)
  have hrk : finrank (X.Kl la) ↥(V'.comap (WL X ka la).subtype) = finrank (X.Kl la) V' :=
    (Submodule.comapSubtypeEquivOfLe hV').finrank_eq
  have hq := qlen_eq_inW X ka la (X.loc la (X.Msup ka)) (X.loc la (X.Theta S ka wL wF T)) V' hV'
  have hle : ThW X S ka wL wF T la ≤ MW X ka la :=
    Submodule.comap_mono (Submodule.span_mono (Set.image_mono hΘM))
  have h0 := qlen_eq_zero_of_le
    (MW X ka la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (ThW X S ka wL wF T la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (inf_le_inf_right _ hle)
  have hfin := qlen_inf_ne_top (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) (ThW X S ka wL wF T la)
    hLat.1 hLat.2 ((V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
  rw [← hq]
  refine ⟨hfin, ?_⟩
  rw [hrk] at hb
  unfold Formalism.LatticeIndexTer.idx at hb
  rw [h0] at hb
  have hb' := hb
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero, Int.cast_natCast] at hb'
  exact hb'

theorem localForm_of_weakForm (h : Thm0LocalW (D := D) (B := B) (P := P) (j := j)) :
    Thm0Local (D := D) (B := B) (P := P) (j := j) := by
  intro large₂ X H S ka wL wF T nus la e hH1 hT hc hTh hTe L hOk V' hV'
  have hW := h large₂ X H S ka wL wF T nus la e hH1 hT hTh hTe L (LocDat.Ok.toW hOk) V' hV'
  first
    | exact hW
    | simpa only [max_eq_right hc] using hW

def Thm0ConclW : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    H1 large₂ X H S wL nus → 1 ≤ T →
    X.Theta S ka wL wF T ≤ X.Msup ka →
    (∀ la, 0 ≤ r la) → Summable (fun la => r la * X.lN la) → (∑' la, r la * X.lN la) ≤ β →
    (∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∃ L : LocDat X ka la, L.OkW S wL wF T e ∧
        L.err T (max 0 (cc D large₂ H.Cc H.Ac H.CRc wL)) ≤ r la) →
    Concl X S ka wL wF T nus β

theorem thm0ConclW : Thm0ConclW (D := D) (B := B) (P := P) (j := j) := by
  intro large₂ X H S ka wL wF T nus β r hH1 hT hle hr hs hb hL
  refine ⟨r, hr, hs, hb, ?_⟩
  intro la e he V' hV
  have h0 : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hH1.1 la)
  have he0 : (0 : ℤ) ≤ e := by
    have : (0 : ℝ) ≤ (e : ℝ) := h0.trans he
    exact_mod_cast this
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le he0
  have he' : (T : ℝ) * nus la ≤ (n : ℝ) := by simpa using he
  obtain ⟨L, hOk, herr⟩ := hL la n he'
  obtain ⟨h1, h2⟩ := thm0LocalW large₂ X H S ka wL wF T nus la n hH1 hT hle he' L hOk V' hV
  refine ⟨h1, ?_⟩
  have h3 : (((n : ℤ) : ℝ)) = (n : ℝ) := by simp
  rw [h3]
  linarith

theorem concl_of_hypW (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ)
    (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus)
    (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la)) (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∃ L : LocDat X ka la, L.OkW S wL wF T e ∧
        L.err T (max 0 (cc D large₂ H.Cc H.Ac H.CRc wL)) ≤ r la) :
    Concl X S ka wL wF T nus β := by
  have hT : 1 ≤ T := by
    obtain ⟨_, hS, _⟩ := hH
    exact (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 : 0 < T)
  exact thm0ConclW large₂ X H S ka wL wF T nus β r hH.2.2.2.1 hT
    (theta_le_msup_of_hyp X S hH) hr0 hrs hrb hloc

end Formalism.MainNotions.Gaps.T0
