import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MoveUpLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem localization_le_localization_of_le {M N : Submodule (𝓞 E) (Sp E n)} (P : HeightOneSpectrum (𝓞 E))
    (h : M ≤ N) : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N :=
  localization_le_of_smul_mem (one_notMem P) fun y hy => by rw [one_smul]; exact h hy

theorem exists_notMem_conj_mem (P : ST) (hP : MoveHyp ST SG P) :
    ∃ a : 𝓞 E, a ∉ P.1.asIdeal ∧ ∀ Q : ST, cO E a ∈ Q.1.asIdeal := by
  classical
  have hex : ∀ Q : ST, ∃ b ∈ Q.1.asIdeal, b ∉ (conjPrime₂ P.1).asIdeal := fun Q =>
    exists_mem_notMem (hP.st Q)
  choose b hb hb' using hex
  refine ⟨cO E (∏ Q : ST, b Q), ?_, fun Q => ?_⟩
  · intro h
    have h' : ∏ Q : ST, b Q ∈ (conjPrime₂ P.1).asIdeal := (mem_conjP _ _).2 h
    obtain ⟨Q, -, hQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (conjPrime₂ P.1).isPrime)).1 h'
    exact hb' Q hQ
  · rw [cO_cO]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem b (Finset.mem_univ Q)) (hb Q)

theorem localization_dual_L_eq_localization_N {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N := by
  obtain ⟨a, ha, haQ⟩ := exists_notMem_conj_mem P hP
  exact le_antisymm (localization_le_of_smul_mem ha fun y hy => hd.smul_Lsh_mem_N haQ hy)
    (localization_le_localization_of_le P.1 hd.N_le_Lsh)

theorem localization_L_eq_localization_kerAt {d : Deco E n ST SG} (hd : d.Ok) (P : ST) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.kerAt P) := by
  ext y
  rw [hd.mem_locP_L]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h1
    refine (mem_locP _ _ _).2 ⟨s, hs, (hd.mem_kerAt P _).2 ⟨hsy, ?_⟩⟩
    rw [hd.f_smul P s y h1, h2, mul_zero]
  · intro h
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P _).1 hsy
    have hy : y ∈ d.at P.1 := (mem_locP _ _ _).2 ⟨s, hs, h1⟩
    refine ⟨hy, ?_⟩
    rw [hd.f_smul P s y hy] at h2
    exact (mul_eq_zero.1 h2).resolve_left (mk_ne_zero hs)

theorem localization_up_L_eq_localization_N {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N := by
  have hd' := hd.up P hP hq hq2 hx hfx
  rw [localization_L_eq_localization_kerAt hd' P, ← (hd'.dnN_spec P hP.ne).2.2.2, hd.dnN_up P hP hq hq2 hx hfx]

theorem localization_dual_up_L {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) (d.up P q x).L) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔
        Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) := by
  have hd' := hd.up P hP hq hq2 hx hfx
  obtain ⟨-, -, -, h4, h5⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  rw [localization_dual_L_eq_localization_N hd' P hP]
  change Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) = _
  have hq0' : q ≠ 0 := fun h => hq2 (h ▸ Submodule.zero_mem _)
  have hq0 : algebraMap (𝓞 E) E q ≠ 0 := by rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  obtain ⟨a, ha, haQ⟩ := exists_notMem_conj_mem P hP
  obtain ⟨b, hb, hbP⟩ := exists_mem_notMem hP.ne
  obtain ⟨c, hc, r, hr, hcr⟩ := exists_inv_unif P.1 hq hq2
  have hAS : upA P.1.asIdeal d.N x ≤
      d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x} := by
    refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    rintro z ⟨e, he, rfl⟩
    obtain ⟨β, hβ⟩ := Formalism.HermitianLatticesTheory.neighbourConstruct_mem_inv.1 he q hq
    have e1 : e • x = β • ((algebraMap (𝓞 E) E q)⁻¹ • x) := by
      rw [← algebraMap_smul E β, smul_smul, hβ, mul_comm (algebraMap (𝓞 E) E q) e, mul_assoc,
        mul_inv_cancel₀ hq0, mul_one]
    rw [SetLike.mem_coe, e1]
    exact (le_sup_right : _ ≤ d.N ⊔ _)
      (Submodule.smul_mem _ β (Submodule.subset_span rfl))
  have hSA : ∀ z ∈ d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x},
      r • z ∈ upA P.1.asIdeal d.N x := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have e2 : r • (t • ((algebraMap (𝓞 E) E q)⁻¹ • x)) = t • (c • x) := by
      rw [smul_comm r t, ← algebraMap_smul E r, smul_smul, ← hcr, mul_comm (algebraMap (𝓞 E) E q) c,
        mul_assoc, mul_inv_cancel₀ hq0, mul_one]
    rw [smul_add, e2]
    exact Submodule.add_mem_sup (d.N.smul_mem r hu)
      (Submodule.smul_mem _ t (Submodule.subset_span ⟨c, hc, rfl⟩))
  have hupN : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upA P.1.asIdeal d.N x) :=
    le_antisymm (localization_le_localization_of_le P.1 h4)
      (localization_le_of_smul_mem hbP fun y hy => h5 (Submodule.smul_mem_smul hb hy))
  have hA : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upA P.1.asIdeal d.N x) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) :=
    le_antisymm (localization_le_localization_of_le P.1 hAS) (localization_le_of_smul_mem hr hSA)
  have hL : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔
        Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) := by
    refine le_antisymm (localization_le_of_smul_mem ha fun z hz => ?_)
      (localization_le_localization_of_le P.1 (sup_le_sup_right hd.N_le_Lsh _))
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
    rw [smul_add]
    exact Submodule.add_mem_sup (hd.smul_Lsh_mem_N haQ hu) (Submodule.smul_mem _ a hv)
  rw [hupN, hA, hL]

theorem lattices_at_up : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E n ST SG), d.Ok → ∀ (P : ST), MoveHyp ST SG P → ∀ (q : 𝓞 E), q ∈ P.1.asIdeal → q ∉ P.1.asIdeal ^ 2 → ∀ (x : Sp E n), x ∈ d.N → d.f P x = 1 → d.N ≤ Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) (d.up P q x).L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) ∧ ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).N, (d.up P q x).f P y = d.f P (q • y) := by
  intro E _ _ _ n ST SG d hd P hP q hq hq2 x hx hfx
  exact ⟨hd.N_le_Lsh, localization_dual_L_eq_localization_N hd P hP, localization_up_L_eq_localization_N hd P hP hq hq2 hx hfx,
    localization_dual_up_L hd P hP hq hq2 hx hfx, fun y hy => by
      rw [Deco.up_f, if_pos (show y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) from hy)]⟩

end GlobalTheory.MoveUpLat
