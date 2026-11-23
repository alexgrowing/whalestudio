import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivGen
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivStmt

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Helpers

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem mem_good_primes_of_no_exceptional (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  have h := P.2
  simp only [rowSG, uSG, hQ, Finset.union_empty] at h
  exact h

theorem levelQ_char_eq_one_of_empty (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {n : ℕ} (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))) (c : ↥Θ.grp) :
    Θ.chr c = 1 := by
  have : IsEmpty {P // P ∈ QE sel (mu : Chr X.F X.E X.K)} := ⟨fun P => by simpa [hQ] using P.2⟩
  simp [LevQFam.chr, piChar]
  rfl

open Classical in
theorem prod_selected_good_eq_prod_good_of_no_exceptional (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {M : Type} [CommMonoid M] (f : {w // w ∈ Pr.vGs} → M) :
    ∏ P : rowSG Pr sel mu, f ⟨P.1, mem_good_primes_of_no_exceptional sel mu hQ P⟩ = ∏ w : {w // w ∈ Pr.vGs}, f w := by
  refine Fintype.prod_equiv
    { toFun := fun P => ⟨P.1, mem_good_primes_of_no_exceptional sel mu hQ P⟩
      invFun := fun w => ⟨w.1, Finset.mem_union_left _ w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } _ _ (fun _ => rfl)

open Classical in

theorem sub_mem_of_ybSet {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    {a a' : Sp X.E n} (ha : a ∈ Y) (ha' : a' ∈ Y) :
    a - a' ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
  obtain ⟨y, -, rfl⟩ := hY
  have e : a - a' = (a - y) - (a' - y) := by abel
  rw [e]
  exact sub_mem ha ha'

open Classical in

theorem nonempty_of_ybSet {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N) :
    Y.Nonempty := by
  obtain ⟨y, -, rfl⟩ := hY
  refine ⟨y, ?_⟩
  show y - y ∈ locLat (rowSG Pr sel mu) N _
  rw [sub_self]
  exact Submodule.zero_mem _

end Helpers

section Alg

theorem inFr_move1 {E : Type} [Field E] {a b : ℕ} (γ F κ : Sp E a ≃ₗ[E] Sp E a) (γ' F' κ' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    inFr (γ * F * κ) (γ' * F' * κ') (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) = κ'.symm.toLinearMap ∘ₗ inFr F F' x ∘ₗ κ.toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq]
  simp only [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem mul_three_symm_apply {E : Type} [Field E] {n : ℕ} (a b c : Sp E n ≃ₗ[E] Sp E n) (v : Sp E n) :
    (a * b * c).symm v = c.symm (b.symm (a.symm v)) := by
  rw [LinearEquiv.symm_apply_eq]
  simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]

theorem prod_mul_eq_of_pointwise_cross {ι K : Type} [Fintype ι] [CommRing K] (a b y z : ι → K) (φ : K) (h : ∀ i, a i * z i = b i * y i) :
    (∏ i, a i) * (φ * ∏ i, z i) = (∏ i, b i) * (φ * ∏ i, y i) := by
  have e : ∏ i, a i * z i = ∏ i, b i * y i := Finset.prod_congr rfl fun i _ => h i
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at e
  calc _ = φ * ((∏ i, a i) * ∏ i, z i) := by ring
    _ = φ * ((∏ i, b i) * ∏ i, y i) := by rw [e]
    _ = _ := by ring

theorem piChar_apply_coe {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    ((piChar H lam x : Kˣ) : K) = ∏ i, ((lam i ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ : Kˣ) : K) := by
  unfold piChar
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  rfl

theorem levelChar_apply_coe {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (Λ : LevFam E K n SG) (x : ↥Λ.grp) :
    ((Λ.chr x : Kˣ) : K) = ∏ w, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : Kˣ) : K) :=
  piChar_apply_coe _ _ x

end Alg

section Inv1

theorem mem_prime_of_mem_divisors {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.mp h
  · simp at h

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word}

theorem frame_mem_lattice_iff_std {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (v : Sp X.E (R.N j)) :
    frsF sel mu p P v ∈ p.deco.1.at P.1 ↔ v ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  rw [dif_pos hP]
  exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, hP⟩)).1 v

open Classical in

theorem frame_inclusion_integral {i : ℕ} (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (w : HomE X.E (R.N i) (R.N (i + 1))) (hw : w ∈ homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) (s : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 ((inFr (frsF sel mu p P) (frsF sel mu p' P) w) (Pi.single s 1) l) := by
  have h1 : frsF sel mu p P (Pi.single s 1) ∈ p.deco.1.at P.1 := (frame_mem_lattice_iff_std sel mu p P hP _).2 (xqSingle_mem (P := P.1) s)
  have h2 := hw P.1 (Finset.mem_union_right _ P.2) _ h1
  have h3 : (frsF sel mu p' P).symm (w (frsF sel mu p P (Pi.single s 1))) ∈ stdAt X.E (R.N (i + 1)) P.1 :=
    (frame_mem_lattice_iff_std sel mu p' P hP _).1 (by rwa [LinearEquiv.apply_symm_apply])
  exact (xqMem_stdAt (P := P.1) _).1 h3 l

open Classical in

theorem modulus_div_prime_pow_integral_bad (P : rowSG Pr sel mu) :
    IntAt P.1 (((Col.qOf P.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) := by
  have hq : (Col.qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (qOf_pos P.1).ne'
  have e : ((cBof sel mu cst u : ℕ) : X.E) =
      (Col.qOf P.1 : X.E) ^ cst.B * (((Pr.T u * (∏ P' ∈ Finset.univ.erase P, Col.qOf P'.1) ^ cst.B : ℕ)) : X.E) := by
    unfold cBof
    rw [← Finset.mul_prod_erase Finset.univ (fun P' : rowSG Pr sel mu => Col.qOf P'.1) (Finset.mem_univ P)]
    push_cast
    ring
  rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  have := xqIntAt_intCast (P := P.1) ((Pr.T u * (∏ P' ∈ Finset.univ.erase P, Col.qOf P'.1) ^ cst.B : ℕ) : ℤ)
  simpa using this

open Classical in

theorem xiCpl1_inv (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (hPr : Pr.Ok) {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2)
    (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (x z : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N)) :
    XiCpl1 Ch sel mu cst L m2 al p₀ p Y (x + z) = XiCpl1 Ch sel mu cst L m2 al p₀ p Y x := by
  obtain ⟨w, hw, rfl⟩ := (mem_mulLat _ _ _).1 hz
  have hphi : phiT X.K p₀.deco.1 p.deco.1 (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w) = phiT X.K p₀.deco.1 p.deco.1 x := by
    refine phiT_add_mul X.K p₀.deco p.deco (Sall sel mu u) (fun P => Finset.mem_union_left _ P.2) (Pr.T u) (fun P => ?_) x _ ?_
    · have h1 : Pr.piT u ∈ P.1.asIdeal := mem_prime_of_mem_divisors P.2
      rw [← hPr.piT_norm u]
      exact P.1.asIdeal.mul_mem_right _ h1
    · refine (mem_mulLat _ _ _).2 ⟨(((∏ P : rowSG Pr sel mu, Col.qOf P.1) ^ cst.B : ℕ) : 𝓞 X.E) • w,
        Submodule.smul_mem _ _ hw, ?_⟩
      rw [smul_smul]
      unfold cBof
      push_cast
      rfl
  have hpsi : ∀ P : rowSG Pr sel mu, PsiAt Ch sel mu cst m2 P (L.h m2 al P)
      (inFr (frsF sel mu p₀ P) (frsF sel mu p P) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) ((frsF sel mu p P).symm (repY Y)) =
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x) ((frsF sel mu p P).symm (repY Y)) := by
    intro P
    have hP := mem_good_primes_of_no_exceptional (Pr := Pr) sel mu hQ P
    have e : inFr (frsF sel mu p₀ P) (frsF sel mu p P) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w) =
        inFr (frsF sel mu p₀ P) (frsF sel mu p P) x + inFr (frsF sel mu p₀ P) (frsF sel mu p P) (((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w) := by
      simp only [inFr, LinearMap.add_comp, LinearMap.comp_add]
    rw [e]
    refine hL.psiInvX al P _ _ _ fun s l => ?_
    have e2 : (inFr (frsF sel mu p₀ P) (frsF sel mu p P) (((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) (Pi.single s 1) l =
        ((cBof sel mu cst u : ℕ) : X.E) * (inFr (frsF sel mu p₀ P) (frsF sel mu p P) w) (Pi.single s 1) l := by
      simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply]
      rw [← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, Pi.smul_apply, smul_eq_mul, map_natCast]
    rw [e2, ← mul_assoc]
    exact (modulus_div_prime_pow_integral_bad sel mu cst P).mul (frame_inclusion_integral sel mu p₀ p P hP w hw s l)
  unfold XiCpl1
  rw [hphi, Finset.prod_congr rfl fun P _ => hpsi P]

theorem chr_ratio_prod1 (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {n n' : ℕ} (Λ : LevFam X.E X.K n Pr.vGs) (Λ' : LevFam X.E X.K n' Pr.vGs)
    (x : ↥Λ.grp) (x' : ↥Λ'.grp) :
    (((Λ'.chr x' * (Λ.chr x)⁻¹ : X.Kˣ)) : X.K) =
      ∏ P : rowSG Pr sel mu,
        (((Λ' ⟨P.1, mem_good_primes_of_no_exceptional sel mu hQ P⟩).lam ⟨(x' : GLG X.E n' Pr.vGs) ⟨P.1, mem_good_primes_of_no_exceptional sel mu hQ P⟩, x'.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
          ((((Λ ⟨P.1, mem_good_primes_of_no_exceptional sel mu hQ P⟩).lam ⟨(x : GLG X.E n Pr.vGs) ⟨P.1, mem_good_primes_of_no_exceptional sel mu hQ P⟩, x.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K) := by
  rw [prod_selected_good_eq_prod_good_of_no_exceptional sel mu hQ (fun w =>
    (((Λ' w).lam ⟨(x' : GLG X.E n' Pr.vGs) w, x'.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
      ((((Λ w).lam ⟨(x : GLG X.E n Pr.vGs) w, x.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K))]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, levelChar_apply_coe, levelChar_apply_coe, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]

open Classical in

theorem psi_at_coupling_representative (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2)
    (al : L.β m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (γ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (hY : Y ∈ ybSet sel mu cst p.deco.1.N) (P : rowSG Pr sel mu)
    (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) :
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ ((frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y)))) =
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ ((frsF sel mu p P).symm (repY Y)) := by
  have hP := mem_good_primes_of_no_exceptional (Pr := Pr) sel mu hQ P
  have hrepY : γ.symm (repY ((fun v => γ v) '' Y)) ∈ Y := by
    obtain ⟨v, hv, hve⟩ : repY ((fun v => γ v) '' Y) ∈ (fun v => γ v) '' Y :=
      Classical.epsilon_spec ((nonempty_of_ybSet sel mu cst hY).image _)
    rw [← hve, LinearEquiv.symm_apply_apply]
    exact hv
  have hrep0 : repY Y ∈ Y := Classical.epsilon_spec (nonempty_of_ybSet sel mu cst hY)
  have hdiff := sub_mem_of_ybSet sel mu cst hY hrepY hrep0
  have hwP : γ.symm (repY ((fun v => γ v) '' Y)) - repY Y ∈ p.deco.1.at P.1 := by
    have := (mem_locLat _ _ _ _).1 hdiff P
    simpa [if_pos hP] using this
  have hz : (frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y)) - repY Y) ∈ stdAt X.E (R.N (m2 + 1)) P.1 :=
    (frame_mem_lattice_iff_std sel mu p P hP _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hwP)
  have hz' := (xqMem_stdAt (P := P.1) _).1 hz
  have e : (frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y))) =
      (frsF sel mu p P).symm (repY Y) + (frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y)) - repY Y) := by
    rw [← map_add, add_sub_cancel]
  rw [e]
  refine hL.psiInv al P x₀ _ _ fun i => ?_
  rw [if_pos hP, pow_zero, inv_one, one_mul]
  exact hz' i

end Inv1

section Cp1Thm

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem cp1EquivOn_of_inv (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (hT : 0 < Pr.T u)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2)
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (hinv : ∀ (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1))
      (Y : Set (Sp X.E (R.N (m2 + 1)))) (x z : HomE X.E (R.N m2) (R.N (m2 + 1))),
      z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N) →
        XiCpl1 Ch sel mu cst L m2 al p₀ p Y (x + z) = XiCpl1 Ch sel mu cst L m2 al p₀ p Y x)
    (hPsi : ∀ al : L.β m2, PsiLaw Ch sel mu cst L m2 al b) :
    Cp1EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY := by
  intro al g₀ g p₀ p (Y : Set (Sp X.E (R.N (m2 + 1)))) hYm
  have hG := mem_good_primes_of_no_exceptional (Pr := Pr) sel mu hQ
  have hYm0 : Y ∈ ybSet sel mu cst p.deco.1.N := hYm
  have hY1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N :=
    (ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm0
  choose κ₀ hκ₀ hκr₀ using fun P : rowSG Pr sel mu =>
    frsF_smul sel mu p₀ (L.levG m2 al) (L.levQ m2 al) g₀ P (hG P)
  choose κ hκ hκr using fun P : rowSG Pr sel mu =>
    frsF_smul sel mu p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g P (hG P)
  have hfr₀ : frsF sel mu (g₀ • p₀) = fun P => g₀.1.1 * frsF sel mu p₀ P * (κ₀ P).1 := funext hκ₀
  have hfr : frsF sel mu (g • p) = fun P => g.1.1 * frsF sel mu p P * (κ P).1 := funext hκ
  have hN₀ : IsSdLat p₀.deco.1.N := ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  have hdeco₀ : (g₀ • p₀).deco = (g₀.1, (g₀.2.1 : GLG X.E (R.N m2) Pr.vGs)) • p₀.deco := rfl
  have hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco := rfl
  have hrep := psi_at_coupling_representative Ch sel mu cst L hQ hL al p g.1.1 Y hYm0
  have hΞ : ∀ x, (∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P (LinearEquiv.det (κ₀ P).1 : X.Eˣ) *
        rhoT Ch sel mu m2 P (LinearEquiv.det (κ P).1 : X.Eˣ)) *
      XiCpl1 Ch sel mu cst L m2 al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y) (g.1.1.toLinearMap ∘ₗ x ∘ₗ g₀.1.1.symm.toLinearMap) =
      ((((L.levG (m2 + 1) b).chr g.2.1 * ((L.levG m2 al).chr g₀.2.1)⁻¹ : X.Kˣ)) : X.K) * XiCpl1 Ch sel mu cst L m2 al p₀ p Y x := by
    intro x
    unfold XiCpl1
    rw [hfr₀, hfr, hdeco₀, hdeco, phiT_smul]
    simp only [inFr_move1, mul_three_symm_apply]
    have hloc : ∀ P : rowSG Pr sel mu,
        rhoS Ch sel mu m2 P (LinearEquiv.det (κ₀ P).1 : X.Eˣ) * rhoT Ch sel mu m2 P (LinearEquiv.det (κ P).1 : X.Eˣ) *
            PsiAt Ch sel mu cst m2 P (L.h m2 al P)
              ((κ P).1.symm.toLinearMap ∘ₗ inFr (frsF sel mu p₀ P) (frsF sel mu p P) x ∘ₗ (κ₀ P).1.toLinearMap)
              ((κ P).1.symm ((frsF sel mu p P).symm (g.1.1.symm (repY ((fun v => g.1.1 v) '' Y))))) =
          (((L.levG (m2 + 1) b ⟨P.1, hG P⟩).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨P.1, hG P⟩, g.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
            ((((L.levG m2 al ⟨P.1, hG P⟩).lam ⟨(g₀.2.1 : GLG X.E (R.N m2) Pr.vGs) ⟨P.1, hG P⟩, g₀.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K) *
            PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x) ((frsF sel mu p P).symm (repY Y)) := fun P => by
      rw [← hrep P (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x)]
      exact hPsi al P (hG P) _ _ (κ₀ P) (κ P) (hκr₀ P) (hκr P) _ _
    have hc := chr_ratio_prod1 sel mu hQ (L.levG m2 al) (L.levG (m2 + 1) b) g₀.2.1 g.2.1
    rw [hc]
    exact prod_mul_eq_of_pointwise_cross _ _ _ _ _ hloc
  have key := kerOf_move (hOk.th m2 le_rfl) (cBof_pos sel mu cst u hT) hN₀ hN (frsF sel mu p₀) (frsF sel mu p) g₀.1 g.1 κ₀ κ
    (XiCpl1 Ch sel mu cst L m2 al p₀ p Y) (XiCpl1 Ch sel mu cst L m2 al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y)) _
    (hinv al p₀ p Y) hΞ
  show cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y) =
    (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g) ∘ₗ
      cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p₀ p Y ∘ₗ
      (frmRho (colValF W sel mu u m2) (L.levG m2 al) (L.levQ m2 al) g₀⁻¹)
  unfold cp1K
  rw [if_pos hY1, if_pos hYm0, hfr₀, hfr]
  refine key.trans ?_
  simp only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, levelQ_char_eq_one_of_empty sel mu hQ, mul_one, Prod.fst_inv, Prod.snd_inv, map_inv,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ring

theorem cp1EquivOn_of (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (hT : 0 < Pr.T u) (hPr : Pr.Ok)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2)
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (hPsi : ∀ al : L.β m2, PsiLaw Ch sel mu cst L m2 al b) :
    Cp1EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY :=
  cp1EquivOn_of_inv W Ch sel mu cst L A u m2 hQ hT hOk hL b hY
    (fun al p₀ p Y x z hz => xiCpl1_inv Ch sel mu cst L hQ hPr hL al p₀ p Y x z hz) hPsi

end Cp1Thm

end Formalism.L2.Ker
