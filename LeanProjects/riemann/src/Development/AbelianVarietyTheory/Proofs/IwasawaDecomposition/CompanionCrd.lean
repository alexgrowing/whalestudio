import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.MemLat

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem mem_N_iff (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal)
    (hcop : IsCoprime π (cO E π)) (x : Sp E n) :
    x ∈ d.N ↔ ∃ a ∈ d.L, ∃ b ∈ d.Lsh, x = a + cO E π • b := by
  constructor
  · intro hx
    obtain ⟨s, t, hst⟩ := hcop
    refine ⟨s • (π • x), d.L.smul_mem s (hd.smul_N_mem_L hmem hx), t • x, d.Lsh.smul_mem t (hd.N_le_Lsh hx), ?_⟩
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (cO E π) t, hst, one_smul]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact d.N.add_mem (hd.L_le_N ha) (hd.smul_Lsh_mem_N (fun P => by rw [cO_cO]; exact hmem P) hb)

theorem std_of_gram (S : HSpace E) {m : ℕ} (h : S.rank = m) (hg : S.gram.reindex (finCongr h) (finCongr h) = 1) (x y : S.V) :
    stdH E m (Crd.co S h x) (Crd.co S h y) = S.hT x y := by
  subst h
  have hg' : ∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun hg a) b
    simpa [HSpace.gram, Matrix.one_apply] using this
  conv_rhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, LinearMap.sum_apply, hg',
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [stdH, Crd.co, starRingEnd_apply]

omit [NumberField E] in
theorem hStd_eq_stdH (x y : Fin n → E) : hStd E n x y = stdH E n x y := rfl

theorem mem_dual_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (b : S.V) :
    b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) (L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) := by
  rw [mem_dual]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  constructor
  · intro H z hz
    obtain ⟨a, ha, rfl⟩ := hz
    have := H a ha
    simpa [hStd_eq_stdH, hco] using this
  · intro H a ha
    have := H (co a) ⟨a, ha, rfl⟩
    simpa [hStd_eq_stdH, hco] using this

theorem companion_crd (S : HSpace E) (co : S.V ≃ₗ[E] (Fin n → E)) (hco : ∀ x y, stdH E n (co x) (co y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (d : Deco E n ST SG) (hd : d.Ok)
    (hL : L.map ((co : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = d.L)
    (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) (y : S.V) :
    co y ∈ d.N ↔ ∃ a ∈ L, ∃ b ∈ Formalism.HermitianLatticesTheory.dual S.hT L, y = a + star (algebraMap (𝓞 E) E π) • b := by
  have hA : ∀ a, a ∈ L ↔ co a ∈ d.L := fun a => by
    rw [← hL]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨z, hz, e⟩ => co.injective e ▸ hz⟩
  have hB : ∀ b, b ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ co b ∈ d.Lsh := fun b => by
    rw [mem_dual_crd S co hco, hL]
    exact Iff.rfl
  have hc : ∀ v : Fin n → E, cO E π • v = star (algebraMap (𝓞 E) E π) • v := fun v => by
    rw [← algebraMap_smul E (cO E π) v, algebraMap_cO]
  rw [mem_N_iff d hd π hmem hcop]
  constructor
  · rintro ⟨a', ha', b', hb', e⟩
    refine ⟨co.symm a', (hA _).2 (by simpa using ha'), co.symm b', (hB _).2 (by simpa using hb'), co.injective ?_⟩
    rw [map_add, map_smul, co.apply_symm_apply, co.apply_symm_apply, e, hc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨co a, (hA a).1 ha, co b, (hB b).1 hb, ?_⟩
    rw [map_add, map_smul, hc]

end Gen

end GlobalTheory.Mem.Col2.MemLat

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Col2.TC.memLatAt_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (O : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).mem u).C), (∀ i c, (O.lat i c).1 = ((I.stp u I.mu0 i).rep c).1.1.deco.1.N) → MemLatAt O (X.piT u) := by
  intro B X I hI hP l Z u O hlat
  obtain ⟨-, -, -, hsp⟩ := spaces_in_coordinates I hI hP l Z
  intro i hi
  obtain ⟨hg, hl0, hL⟩ := hsp i hi
  have hL' := (hL u I.mu0).1
  set co := GlobalTheory.Mem.Col2.Crd.co ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) with hco
  have hiso := GlobalTheory.Mem.Col2.MemLat.std_of_gram _ _ hg
  refine ⟨co, hiso, ?_, ?_⟩
  · intro y
    rw [O.lattice_integral_coordinates]
    have h1 : co y ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ y ∈ ((I.rec7 l Z).sp.X i).L0 :=
      ⟨fun ⟨z, hz, e⟩ => co.injective e ▸ hz, fun h => ⟨y, h, rfl⟩⟩
    rw [← h1, hl0]
    refine forall_congr' fun k => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, ?_⟩
    rintro ⟨r, hr⟩
    rw [← hr]
    exact RingOfIntegers.isIntegral_coe r
  · intro c y
    rw [hlat i c]
    have hsep := sepElt_of_ok l.pr u
    have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
      have := hsep.conj P
      rwa [cO_cO] at this
    have hLm : ((I.rec7 l Z).clsLat u i c).map ((co : ((I.rec7 l Z).sp.X i).V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) =
        (((I.stp u I.mu0 i).rep c).1.1.deco).1.L := hL' c
    refine (GlobalTheory.Mem.Col2.MemLat.companion_crd _ co hiso _ (((I.stp u I.mu0 i).rep c).1.1.deco).1 (((I.stp u I.mu0 i).rep c).1.1.deco).2
      hLm ((B.primes X).piT u) hmem (l.pr.piT_cop u) y).trans ?_
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]
