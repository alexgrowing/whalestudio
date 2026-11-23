import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.NormalFormInclusion

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Proof.NormalFormAtPrime

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Arith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem degOne_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) (hv : DegOne v)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) : DegOne P := by
  have key : ∀ Q Q' : HeightOneSpectrum (𝓞 E), Q ≠ Q' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal → Q.asIdeal.under (𝓞 F) = v.asIdeal → DegOne Q := by
    intro Q Q' hne hm hQ
    have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← map_mul, ← hm, Ideal.absNorm_algebraMap, ← h2]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm
    have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have hq : Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal :=
      (((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1)
    refine ⟨hq ▸ hv.1, ?_⟩
    rw [hq]
    intro hmem
    have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
    obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
      Ideal.dvd_span_singleton.2 hqv
    have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
      exact Ideal.dvd_span_singleton.2 hmem
    rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
    rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
    · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
    · have hle : I ≤ v.asIdeal := by
        rw [← hQ]
        exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
      apply hv.2
      rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
      exact Ideal.mul_mono_right hle
  obtain ⟨Q, Q', hne, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, ← hP]
    exact Ideal.map_comap_le
  rcases P.isPrime.mul_le.1 hle with h | h
  · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    exact key _ _ hne hm hP
  · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    exact key _ _ hne.symm (by rw [hm, mul_comm]) hP

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  have : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast this

theorem intAt_pow_mul {P : HeightOneSpectrum (𝓞 E)} (k : ℕ) {a : E} (ha : IntAt P a) : IntAt P ((qOf P : E) ^ k * a) := by
  refine IntAt.mul ?_ ha
  simpa using IntAt.coe P ((qOf P : 𝓞 E) ^ k)

theorem intAt_pow_mono {P : HeightOneSpectrum (𝓞 E)} {A A' : ℕ} (h : A ≤ A') {a : E} (ha : IntAt P ((qOf P : E) ^ A * a)) :
    IntAt P ((qOf P : E) ^ A' * a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := intAt_pow_mul k ha
  rwa [← mul_assoc, ← pow_add, add_comm] at this

theorem intAt_inv_pow_anti {P : HeightOneSpectrum (𝓞 E)} {B B' : ℕ} (h : B ≤ B') {a : E}
    (ha : IntAt P (((qOf P : E) ^ B')⁻¹ * a)) : IntAt P (((qOf P : E) ^ B)⁻¹ * a) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have := intAt_pow_mul k ha
  have hq := qOf_ne_zero P
  convert this using 1
  field_simp
  ring

end Arith

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem nfLat_eq {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ) (e : Fin c → ℤ)
    (z : Sp E n) : IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z = (IndefiniteRowSideFullHecke.NormalFormInclusion.nfLat P (qOf P) n c e z : Set (Sp E (n + c))) := by
  ext y
  simp only [IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat, IndefiniteRowSideFullHecke.NormalFormInclusion.nfLat, Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_sup, Submodule.mem_map]
  constructor
  · rintro ⟨l, hl, s, hs, rfl⟩
    exact ⟨_, ⟨l, hl, rfl⟩, _, ⟨s, (mem_localization_standardLattice P _).2 hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨l, hl, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨l, hl, s, (mem_localization_standardLattice P _).1 hs, rfl⟩

theorem nf_iff (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) :
    IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h ↔ IndefiniteRowSideFullHecke.NormalFormInclusion.NF Pr j P h := by
  refine exists_congr fun e => exists_congr fun z => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [nfLat_eq]
  exact SetLike.coe_set_eq (p := gmap h (lamYat (Pr := Pr) (R := R) j P))

theorem incl_iff : IndefiniteRowSideFullHecke.SandwichNormalForm.InclAt Pr R ↔ IndefiniteRowSideFullHecke.NormalFormInclusion.NFIncl X Pr R := by
  constructor
  · intro H j P hP h hh k hk
    obtain ⟨h1, h2⟩ := H j P hP h k ((nf_iff j P h).2 hh) hk
    exact ⟨fun x hx => h1 x hx, h2⟩
  · intro H j P hP h k hh hk
    obtain ⟨h1, h2⟩ := H j P hP h ((nf_iff j P h).1 hh) k hk
    exact ⟨fun x hx => h1 hx, h2⟩

theorem sameDC_refl (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : SameDC (Pr := Pr) sharp j P h h :=
  ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem sameDC_trans {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h₁ h₂ : AutY X R j}
    (a : SameDC (Pr := Pr) sharp j P h h₁) (b : SameDC (Pr := Pr) sharp j P h₁ h₂) : SameDC (Pr := Pr) sharp j P h h₂ := by
  obtain ⟨r, hr, k, hk, rfl⟩ := a
  obtain ⟨r', hr', k', hk', rfl⟩ := b
  exact ⟨r' * r, mul_mem hr' hr, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

def TwistDegOne (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) : Prop :=
  ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → DegOne P.1

theorem twistDegOne_of_isSel (h2 : Module.finrank X.F X.E = 2) (hsel : IsSel X sel) : TwistDegOne Pr sel mu := by
  classical
  rintro ⟨P, hP⟩ hn
  have hQ : P ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.1 hP).resolve_left hn
  unfold QE at hQ
  split_ifs at hQ with hf
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ
    have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := hf.mem_toFinset.1 hv
    have hg : GoodPl X.E S v := by
      by_contra hg
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 mu.2.2 v)) hg
      exact hv' this
    exact degOne_of_split h2 hg.1 hg.2.1 (hsel v)
  · simp at hQ

theorem rep_iff (hd : TwistDegOne Pr sel mu) :
    IndefiniteRowSideFullHecke.SandwichNormalForm.RepAt Ch sel mu ↔ ∀ cst : LocCst X (rowSG Pr sel mu), IndefiniteRowSideFullHecke.NormalFormInclusion.RepExists Ch sel mu cst := by
  classical
  constructor
  · intro H cst hc i hi P hP _ hal hnf h h₁ hs ⟨d, hadd, hint⟩ hE
    have hc' : LocCst.Ok { cst with D := Function.update cst.D P (max d (cst.D P)) } := by
      refine ⟨fun P' x y hx hy => ?_, hc.psi_int, hc.psi_ne, fun P' => ?_, hc.sq_sq, hc.M_pos, hc.M_le_A, hc.M_le_B, hc.B_pos⟩
      · by_cases e : P' = P
        · subst e
          simp only [Function.update_self] at hx hy
          rcases le_total d (cst.D P') with l | l
          · rw [max_eq_right l] at hx hy
            exact hc.psi_add P' x y hx hy
          · rw [max_eq_left l] at hx hy
            exact hadd x y hx hy
        · simp only [Function.update_of_ne e] at hx hy
          exact hc.psi_add P' x y hx hy
      · by_cases e : P' = P
        · subst e
          simp only [Function.update_self]
          exact le_max_of_le_right (hc.D_pos P')
        · simp only [Function.update_of_ne e]
          exact hc.D_pos P'
    obtain ⟨h', hs', hn'⟩ := H _ hc' i hi P hP hal h₁ ((nf_iff _ _ _).2 hnf) (fun x hx => by
      have := hint x hx
      rw [IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP] at this ⊢
      intro l
      simp only [Function.update_self]
      exact intAt_pow_mono (le_max_left _ _) (this l)) hE
    exact ⟨h', sameDC_trans hs hs', (nf_iff _ _ _).1 hn'⟩
  · intro H cst hc i hi P hP hal h hnf hint hE
    obtain ⟨h', hs', hn'⟩ := H cst hc i hi P hP (hd P hP) hal ((nf_iff _ _ _).1 hnf) h h (sameDC_refl _ _ _ _)
      ⟨cst.D P, hc.psi_add P, hint⟩ hE
    exact ⟨h', hs', (nf_iff _ _ _).2 hn'⟩

theorem idxNF_iff (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) :
    IndefiniteRowSideFullHecke.SandwichNormalForm.IdxNF sel mu L ↔ IndefiniteRowSideFullHecke.NormalFormInclusion.IdxNF sel mu L :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => nf_iff _ _ _

variable {Ch sel mu}

theorem ok_mono {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (H : L.Ok Ch sel mu cst G m2) {A' B' : ℕ} (hA : cst.A ≤ A') (hB : cst.B ≤ B') :
    L.Ok Ch sel mu { cst with A := A', B := B' } G m2 := by
  have hX : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu) (x : HomE X.E (R.N i) (R.N (i + 1))),
      XiAt Ch sel mu { cst with A := A', B := B' } i P (L.h i al P) (L.h (i + 1) be P) x =
        XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
    intro i hi al be P x
    unfold XiAt
    rw [H.deep A' B' hA hB i hi al be P]
  exact { H with
    cst_ok := ⟨H.cst_ok.psi_add, H.cst_ok.psi_int, H.cst_ok.psi_ne, H.cst_ok.D_pos, H.cst_ok.sq_sq, H.cst_ok.M_pos,
      H.cst_ok.M_le_A.trans hA, H.cst_ok.M_le_B.trans hB, H.cst_ok.B_pos.trans hB⟩
    deep := fun A'' B'' h1 h2 i hi al be P =>
      (H.deep A'' B'' (hA.trans h1) (hB.trans h2) i hi al be P).trans (H.deep A' B' hA hB i hi al be P).symm
    xiSupp := fun i hi al be P x hx s l => intAt_pow_mono hA (H.xiSupp i hi al be P x (by rwa [hX i hi] at hx) s l)
    xiInv := fun i hi al be P x z hz => by
      rw [hX i hi, hX i hi]
      exact H.xiInv i hi al be P x z fun s l => intAt_inv_pow_anti hB (hz s l)
    psiSuppX := fun al P x y hx s l => intAt_pow_mono hA (H.psiSuppX al P x y hx s l)
    psiInvX := fun al P x z y hz => H.psiInvX al P x z y fun s l => intAt_inv_pow_anti hB (hz s l) }

theorem ok_reindex {cst : LocCst X (rowSG Pr sel mu)} {L L' : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m}
    {m2 : ℕ} (H : L'.Ok Ch sel mu cst G m2) (e : ∀ j, L.β j ≃ L'.β j) (hG : ∀ j (b : L.β j), L'.levG j (e j b) = L.levG j b) :
    ChIdx.Ok Ch sel mu cst { L with h := fun j b => L'.h j (e j b), levQ := fun j b => L'.levQ j (e j b) } G m2 where
  hm := H.hm
  cst_ok := H.cst_ok
  xiUnitAtPrime := H.xiUnitAtPrime
  weil := H.weil
  muqQ := H.muqQ
  muqG := H.muqG
  mu0G := H.mu0G
  psi0 := H.psi0
  deep := fun A B h1 h2 i hi al be P => H.deep A B h1 h2 i hi (e _ al) (e _ be) P
  zero_uniq := by
    obtain ⟨b, hb⟩ := H.zero_uniq
    exact ⟨(e 0).symm b, fun b' => (e 0).eq_symm_apply.2 (hb _)⟩
  zero_h := fun b P => H.zero_h (e _ b) P
  zero_G := fun b => (hG 0 b).symm.trans (H.zero_G (e _ b))
  zero_Q := fun b => H.zero_Q (e _ b)
  last_uniq := by
    obtain ⟨b, hb⟩ := H.last_uniq
    exact ⟨(e _).symm b, fun b' => (e _).eq_symm_apply.2 (hb _)⟩
  last_h := fun b P => H.last_h (e _ b) P
  nonvan := fun i hi b P => by
    obtain ⟨al, hal⟩ := H.nonvan i hi (e _ b) P
    obtain ⟨al, rfl⟩ := (e i).surjective al
    exact ⟨al, hal⟩
  inj := fun i hi b b' hb => (e _).injective (H.inj i hi (e _ b) (e _ b') hb)
  surj := fun i hi hh h1 h2 h3 => by
    obtain ⟨b, hb⟩ := H.surj i hi hh h1 h2 fun P => (h3 P).elim fun al hal => ⟨e i al, hal⟩
    obtain ⟨b, rfl⟩ := (e (i + 1)).surjective b
    exact ⟨b, hb⟩
  stabG := fun j b P => H.stabG j (e _ b) P
  depthG := H.depthG
  depthQ := H.depthQ
  depthQ' := H.depthQ'
  boundQ := fun j b P => H.boundQ j (e _ b) P
  psiSupp := fun al => H.psiSupp (e _ al)
  psiInv := fun al => H.psiInv (e _ al)
  xiSupp := fun i hi al be => H.xiSupp i hi (e _ al) (e _ be)
  xiInv := fun i hi al be => H.xiInv i hi (e _ al) (e _ be)
  psiSuppX := fun al => H.psiSuppX (e _ al)
  psiInvX := fun al => H.psiInvX (e _ al)
  int := fun j b => H.int j (e _ b)
  grpQ := fun j b => H.grpQ j (e _ b)
  chrQ := fun j b => H.chrQ j (e _ b)
  grpG := fun j b => by
    have := H.grpG j (e _ b)
    rw [hG] at this
    exact this
  chrG := fun j b => by
    have := H.chrG j (e _ b)
    rw [hG] at this
    exact this

variable (Ch sel mu)

theorem choice_iff (hd : TwistDegOne Pr sel mu) :
    IndefiniteRowSideFullHecke.SandwichNormalForm.ChoiceAt Ch sel mu ↔ ∀ cst : LocCst X (rowSG Pr sel mu), IndefiniteRowSideFullHecke.NormalFormInclusion.ChoiceExists Ch sel mu cst := by
  refine forall_congr' fun cst => ?_
  constructor
  · intro H _ G m2 L hL
    obtain ⟨A', B', L', e, -, -, hok, hnf, hdc, hg, hlev⟩ := H G m2 L hL
    refine ⟨fun j b => L'.h j (e j b), fun j b => L'.levQ j (e j b), A', B', hdc, hg, ?_, fun A'' B'' h1 h2 => ?_⟩
    · exact fun j h1 h2 b P hP => (nf_iff _ _ _).1 (hnf j h1 h2 (e j b) P hP)
    · exact ok_mono (ok_reindex hok e hlev) h1 h2
  · intro H G m2 L hL
    obtain ⟨h', lq, A₀, B₀, hdc, hg, hnf, hok⟩ := H hd G m2 L hL
    exact ⟨max A₀ cst.A, max B₀ cst.B, { L with h := h', levQ := lq }, fun _ => Equiv.refl _, le_max_right _ _, le_max_right _ _,
      hok _ _ (le_max_left _ _) (le_max_left _ _), (idxNF_iff sel mu _).2 hnf, hdc, hg, fun _ _ => rfl⟩

theorem body_iff (hd : TwistDegOne Pr sel mu) :
    (IndefiniteRowSideFullHecke.SandwichNormalForm.InclAt Pr R ∧ IndefiniteRowSideFullHecke.SandwichNormalForm.RepAt Ch sel mu ∧ IndefiniteRowSideFullHecke.SandwichNormalForm.ChoiceAt Ch sel mu) ↔
      (IndefiniteRowSideFullHecke.NormalFormInclusion.NFIncl X Pr R ∧ ∀ cst : LocCst X (rowSG Pr sel mu),
        IndefiniteRowSideFullHecke.NormalFormInclusion.RepExists Ch sel mu cst ∧ IndefiniteRowSideFullHecke.NormalFormInclusion.ChoiceExists Ch sel mu cst) := by
  rw [incl_iff, rep_iff Ch sel mu hd, choice_iff Ch sel mu hd, ← forall_and]

def NormalFormAtQGuarded : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S),
    Module.finrank X.F X.E = 2 → IsSel X sel →
    IndefiniteRowSideFullHecke.NormalFormInclusion.NFIncl X Pr R ∧ ∀ cst : LocCst X (rowSG Pr sel mu),
      IndefiniteRowSideFullHecke.NormalFormInclusion.RepExists Ch sel mu cst ∧ IndefiniteRowSideFullHecke.NormalFormInclusion.ChoiceExists Ch sel mu cst

theorem normalForm_equiv :
    (∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
      (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S),
      Module.finrank X.F X.E = 2 → IsSel X sel →
      ((IndefiniteRowSideFullHecke.SandwichNormalForm.InclAt Pr R ↔ IndefiniteRowSideFullHecke.NormalFormInclusion.NFIncl X Pr R) ∧
        (IndefiniteRowSideFullHecke.SandwichNormalForm.RepAt Ch sel mu ↔ ∀ cst : LocCst X (rowSG Pr sel mu), IndefiniteRowSideFullHecke.NormalFormInclusion.RepExists Ch sel mu cst) ∧
        (IndefiniteRowSideFullHecke.SandwichNormalForm.ChoiceAt Ch sel mu ↔ ∀ cst : LocCst X (rowSG Pr sel mu), IndefiniteRowSideFullHecke.NormalFormInclusion.ChoiceExists Ch sel mu cst))) ∧
    (IndefiniteRowSideFullHecke.SandwichNormalForm.NormalForm ↔ NormalFormAtQGuarded) ∧
    (IndefiniteRowSideFullHecke.NormalFormInclusion.NormalFormAtQ → IndefiniteRowSideFullHecke.SandwichNormalForm.NormalForm) := by
  have h : IndefiniteRowSideFullHecke.SandwichNormalForm.NormalForm ↔ NormalFormAtQGuarded :=
    forall_congr' fun X => forall_congr' fun Pr => forall_congr' fun R => forall_congr' fun Ch => forall_congr' fun sel =>
      forall_congr' fun S => forall_congr' fun mu => forall_congr' fun h2 => forall_congr' fun hs =>
        body_iff Ch sel mu (twistDegOne_of_isSel sel mu h2 hs)
  refine ⟨fun X Pr R Ch sel S mu h2 hs => ⟨incl_iff, rep_iff Ch sel mu (twistDegOne_of_isSel sel mu h2 hs),
    choice_iff Ch sel mu (twistDegOne_of_isSel sel mu h2 hs)⟩, h, fun H => h.2 fun X Pr R Ch sel S mu _ _ =>
      ⟨(H X Pr R).1, fun cst => (H X Pr R).2 Ch sel S mu cst⟩⟩

end GlobalTheory.Proof.NormalFormAtPrime
