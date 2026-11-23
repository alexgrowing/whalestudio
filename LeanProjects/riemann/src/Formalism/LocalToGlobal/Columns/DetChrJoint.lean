import Mathlib
import Formalism.LocalToGlobal.Columns.DetChrLeaves
import Formalism.LocalToGlobal.Columns.HeckeExHost
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
import Formalism.LocalToGlobal.Divisibility.TuplesLemmas

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Joint

open Classical

variable {X : Fields} {Pr : Primes X}

theorem trivialTuple_coe (S : Set ℕ) : ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = 1 := rfl

theorem twistPrimes_trivialTuple_empty (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) :
    QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = ∅ := by
  unfold QE Qprime
  split_ifs with h
  · rw [Finset.image_eq_empty, Set.Finite.toFinset_eq_empty]
    ext v
    simp [trivialTuple_coe]
  · rfl

theorem conjP_vGs (hX : X.Ok) (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) :
    HeckeExHost.conjPrime₂ P ≠ P ∧ HeckeExHost.conjPrime₂ P ∉ Pr.vGs := by
  have hmem : ∀ j, P ∈ Pr.vG j → X.conjO (Pr.piG j) ∈ P.asIdeal := fun j h => ChainCounts.mem_of_mem_divs h
  have hcomap : ∀ y : 𝓞 X.E, y ∈ (HeckeExHost.conjPrime₂ P).asIdeal ↔ X.conjO y ∈ P.asIdeal := fun y => Iff.rfl
  have hcop : ∀ j, Pr.piG j ∈ P.asIdeal → X.conjO (Pr.piG j) ∈ P.asIdeal → False := by
    intro j h1 h2
    obtain ⟨a, b, hab⟩ := hPr.piG_cop j
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Pr.piG i ∈ (HeckeExHost.conjPrime₂ P).asIdeal := (hcomap _).2 (hmem i hi)
    rw [h] at h1
    exact hcop i h1 (hmem i hi)
  · obtain ⟨j, hj⟩ : ∃ j, HeckeExHost.conjPrime₂ P ∈ Pr.vG j := by
      rcases Finset.mem_union.1 h with h' | h'
      · exact ⟨0, h'⟩
      · exact ⟨1, h'⟩
    have h1 : Pr.piG j ∈ P.asIdeal := by
      have := (hcomap _).1 (ChainCounts.mem_of_mem_divs hj)
      rwa [HeckeExHost.conjO_conjO'] at this
    by_cases hij : j = i
    · subst hij
      exact hcop j h1 (hmem j hi)
    · have hg1 : ((Pr.g j : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm j]
        exact Ideal.mul_mem_right _ _ h1
      have hg2 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i]
        exact Ideal.mul_mem_left _ _ (hmem i hi)
      have hne : Pr.g j ≠ Pr.g i := by
        have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
        rcases key j i hij with ⟨h0, h1'⟩ | ⟨h0, h1'⟩
        · rw [h0, h1']; exact hPr.g_ne
        · rw [h0, h1']; exact hPr.g_ne.symm
      have hcopZ : Nat.Coprime (Pr.g j) (Pr.g i) := (Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (Pr.g j : ℤ) + b * (Pr.g i : ℤ) = 1 := by
        refine ⟨Nat.gcdA (Pr.g j) (Pr.g i), Nat.gcdB (Pr.g j) (Pr.g i), ?_⟩
        have := Nat.gcd_eq_gcd_ab (Pr.g j) (Pr.g i)
        rw [hcopZ] at this
        push_cast at this
        linarith
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 X.E) = (a : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) + (b : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 X.E)) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hg1) (Ideal.mul_mem_left _ _ hg2)

end Joint

section Core

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem core (h1 : HilbertNinetyDeterminant) (h3 : DetAtP) (h2 : CharFactor) {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))} {Dc : DetChr X R.m} {hc : Formalism.BasicNotions.CMData X.F X.E}
    (hX : X.Ok) (hPr : Pr.Ok) (hsel : ∀ v, (sel v).asIdeal.under (𝓞 X.F) = v.asIdeal)
    (hLoc : Dc.Loc Ch sel (mu0 X.F X.E X.K S) cst hc.sig) {i : ℕ} (hi : i < R.m) {N : ℕ} [NeZero N]
    {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet X.E N ST Pr.vGs)
    (hdec : decoOf ST Pr.vGs (ptOf hc N ST Pr.vGs p : GL (Fin N) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) = p) :
    (((detTw hc.sig (Dc.muAt i) (ptOf hc N ST Pr.vGs p : GL (Fin N) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ : X.Kˣ) : X.K) =
      muInvDet sel (rowSG Pr sel (mu0 X.F X.E X.K S)) (mUof Ch (mu0 X.F X.E X.K S) i) (muAt Ch sel (mu0 X.F X.E X.K S) cst i) p.1.N
        (frsD sel (mu0 X.F X.E X.K S) p) := by
  set mu := mu0 X.F X.E X.K S with hmu
  set SB := rowSG Pr sel mu with hSBdef
  set ξ : Chr X.F X.E X.K := Dc.muAt i * (mu : Chr X.F X.E X.K) with hξdef
  have hξ' : ξ = Dc.muAt i := by rw [hξdef, hmu, trivialTuple_coe, mul_one]
  set g : GL (Fin N) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F) := (ptOf hc N ST Pr.vGs p : GL (Fin N) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) with hgdef
  have hg : g ∈ UAd hc N := (ptOf hc N ST Pr.vGs p).2
  obtain ⟨x, hx⟩ := h1 X.F X.E hc N g hg
  have htriv : (h90 hc.sig).ker ≤ ξ.ker := hLoc.trivF i hi
  have hdet : detTw hc.sig (Dc.muAt i) g = ξ x := by
    rw [← hξ']
    exact Formalism.L2.DIV.detTw_of_det hc.sig ξ htriv g x hx
  have hSB : SB = Pr.vGs := ChainCounts.rowSG_eq_of_QE sel mu (twistPrimes_trivialTuple_empty sel S)
  obtain ⟨hfr, hunitL, hcongL⟩ := h3 X.F X.E hc N ST Pr.vGs g hg
  rw [hdec] at hfr hunitL hcongL

  have hframe : ∀ P : HeightOneSpectrum (𝓞 X.E), ∀ z, frameAt P p.1.N z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.1.N ↔ z ∈ stdAt X.E N P := by
    intro P
    obtain ⟨f, hf⟩ := hfr P
    exact Classical.epsilon_spec (p := fun f : Sp X.E N ≃ₗ[X.E] Sp X.E N => ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.1.N ↔ z ∈ stdAt X.E N P) ⟨f, hf⟩
  have hfrs : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (h : P ∈ SB), ∃ hw : P ∈ Pr.vGs, frsD sel mu p ⟨P, h⟩ = p.1.liftFr ⟨P, hw⟩ := by
    intro P h
    have hw : P ∈ Pr.vGs := hSB ▸ h
    exact ⟨hw, by unfold frsD; rw [dif_pos hw]⟩
  have hlift : ∀ w : Pr.vGs, ∀ z, p.1.liftFr w z ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal p.1.N ↔ z ∈ stdAt X.E N w.1 :=
    fun w => (Deco.liftFr_spec (p.2.hasLift w)).1

  let a : HeightOneSpectrum (𝓞 X.E) → X.Eˣ := fun P =>
    if h : P ∈ SB then LinearEquiv.det (frsD sel mu p ⟨P, h⟩) else LinearEquiv.det (frameAt P p.1.N)
  have haS : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (h : P ∈ SB), a P = LinearEquiv.det (frsD sel mu p ⟨P, h⟩) :=
    fun P h => dif_pos h
  have haN : ∀ P : HeightOneSpectrum (𝓞 X.E), P ∉ SB → a P = LinearEquiv.det (frameAt P p.1.N) := fun P h => dif_neg h
  have hunit : ∀ P : HeightOneSpectrum (𝓞 X.E), UnitAtI P (h90 hc.sig x * (ratId X.F X.E (a P))⁻¹) := by
    intro P
    rw [hx]
    by_cases h : P ∈ SB
    · obtain ⟨hw, he⟩ := hfrs P h
      rw [haS P h, he]
      exact hunitL P _ (hlift ⟨P, hw⟩)
    · rw [haN P h]
      exact hunitL P _ (hframe P)
  have hcong : ∀ P ∈ SB, CongOneAtI P ((h90 hc.sig x * (ratId X.F X.E (a P))⁻¹ : (AfE X.F X.E)ˣ) : AfE X.F X.E) := by
    intro P h
    rw [hx]
    obtain ⟨hw, he⟩ := hfrs P h
    rw [haS P h, he]
    exact hcongL ⟨P, hw⟩

  have hfin : {P : HeightOneSpectrum (𝓞 X.E) | ordE P (a P : X.E) ≠ 0}.Finite := by
    have hF := frame_det_unit_almost_all_primes (E := X.E) N p.1.N ⟨p.2.lat, p.2.uni⟩
    refine (hF.union (SB : Set (HeightOneSpectrum (𝓞 X.E))).toFinite).subset ?_
    intro P hP
    by_cases h : P ∈ SB
    · exact Or.inr h
    · left
      show ordDet P p.1.N ≠ 0
      have := hP
      simp only [Set.mem_ofPred_eq] at this
      rw [haN P h] at this
      exact this

  let k : HeightOneSpectrum (𝓞 X.E) → X.Kˣ := fun P =>
    if h : P ∈ SB then Classical.choose (hLoc.atq_ex i hi ⟨P, h⟩) else 1
  have hk : ∀ P (h : P ∈ SB), IsQValC ξ P (k P) := by
    intro P h
    show IsQValC ξ P (if h : P ∈ SB then Classical.choose (hLoc.atq_ex i hi ⟨P, h⟩) else 1)
    rw [dif_pos h]
    exact Classical.choose_spec (hLoc.atq_ex i hi ⟨P, h⟩)
  let χ : ∀ P : HeightOneSpectrum (𝓞 X.E), (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ := fun P =>
    if P ∈ Pr.vGs then (chiP Ch P i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P

  have hsplit : ∀ P ∈ SB, ∃ P' : HeightOneSpectrum (𝓞 X.E), P' ≠ P ∧ P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F) ∧ P' ∉ SB := by
    intro P h
    have hw : P ∈ Pr.vGs := hSB ▸ h
    obtain ⟨hne, hnot⟩ := conjP_vGs hX hPr hw
    refine ⟨HeckeExHost.conjPrime₂ P, hne, ?_, by rw [hSB]; exact hnot⟩
    exact congrArg HeightOneSpectrum.asIdeal (HeckeExHost.conjP_under hX P)
  have hfac := h2 X.F X.E X.K hc ξ SB sel (fun P => (mUof Ch mu i P)⁻¹) χ k a x hsel hsplit
    (fun P h => ChainCounts.unifG_of hX hPr P (hSB ▸ h)) htriv (hLoc.unr i hi) (fun P h => hLoc.unif i hi P h)
    (fun P h v hv => hLoc.tame i hi P h v hv) (fun P h => hLoc.res i hi ⟨P, h⟩) hk hfin hunit hcong
  rw [hdet, hfac]
  unfold muInvDet muOff
  congr 1
  · refine finprod_congr fun v => ?_
    split_ifs with hv
    · rfl
    · have hsv : sel v ∉ SB := fun h => hv ⟨sel v, h, hsel v⟩
      rw [inv_inv, haN (sel v) hsv]
      rfl
  · rw [← Finset.prod_coe_sort SB]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [haS P.1 P.2]
    have hq := hLoc.atq i hi P (k P.1) (hk P.1 P.2)
    unfold muAt
    rw [hq]
    congr 1
    change ((if P.1 ∈ Pr.vGs then (chiP Ch P.1 i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P.1) : (𝓞 X.E ⧸ P.1.asIdeal)ˣ →* X.Kˣ)⁻¹ = _
    split_ifs <;> simp [hmu]

theorem muDetOfLoc_of_leaves (h1 : HilbertNinetyDeterminant) (h3 : DetAtP) (h2 : CharFactor) : MuDetOfLoc := by
  intro X Pr R Ch sel S cst Dc hc u hX hPr hsel hLoc hPt i hi n hn p
  have hnm : n ≤ R.m := by rcases hn with rfl | rfl <;> omega
  exact core h1 h3 h2 hX hPr hsel hLoc hi p (hPt n hnm p)

end Core

end DetChrL

end Formalism.L2.Col
