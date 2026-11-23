import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLOneEqDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompanionCrd
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (h : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
      ((y⁻¹ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ x ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Λ := by
  apply le_antisymm
  · rw [Formalism.L2.PairingIndexBounds.F.latAd, Submodule.span_le]
    intro x hx
    exact Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) Λ hfin x ((h _).2 hx)
  · intro x hx
    exact Submodule.subset_span ((h _).1 (Submodule.subset_span ⟨x, hx, rfl⟩))

theorem GlobalTheory.Mem.Col2.AdT.mvL_one {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.MainNotions.G.KAat.mvL (1 : GL (Fin N) E) Λ = Λ := by
  ext x
  simp only [Formalism.MainNotions.G.KAat.mvL, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Formalism.MainNotions.G.KAat.toLE_apply, Units.val_one, Matrix.one_mulVec, exists_eq_right]

theorem GlobalTheory.Mem.Col2.AdT.sup_dual_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : Deco E n ST SG) (hd : d.Ok) (π : 𝓞 E) (hmem : ∀ P : ST, π ∈ P.1.asIdeal) (hcop : IsCoprime π (cO E π)) :
    d.L ⊔ Ideal.span {cO E π} • Formalism.HermitianLatticesTheory.dual (hStd E n) d.L = d.N := by
  ext x
  rw [GlobalTheory.Mem.Col2.MemLat.mem_N_iff d hd π hmem hcop, Submodule.mem_sup, Submodule.ideal_span_singleton_smul]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact ⟨y, hy, b, hb, rfl⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨y, hy, _, Submodule.smul_mem_pointwise_smul _ _ _ hb, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Col2.AdT.lat_rep_eq_latCo : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ c : (I.stp u a i).Cl, ((I.stp u a i).rep c).1.1.deco.1.N = GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) ((K (chOf c)).y ⟨c, rfl⟩).1 (K (chOf c)).lev.Lb := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K k hR c
  have hsp := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hG := hsp.1
  have hL := (hsp.2.2 u a).1 c
  have hf := (l.lat u a i c).fg
  rw [← hL] at hf
  have hA := (GlobalTheory.Mem.Col2.AdT.latAd_eq_of_latS _ _ _ (Module.Finite.iff_fg.2 hf)
      ((K (chOf c)).y_lat ⟨c, rfl⟩)).trans hL
  unfold GlobalTheory.TwU.latCo
  rw [hA, hG]
  unfold Formalism.L2.PairingIndexBounds.F.compan
  rw [GlobalTheory.Mem.Col2.AdT.mvL_one]
  have key := GlobalTheory.Mem.Col2.TC.dualL_one_eq_dual (((I.rec7 l Z).sp.cm.sig : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E))
    (fun x => rfl) ((I.stp u a i).rep c).1.1.deco.1.L
  unfold dualL at key
  erw [key]
  have hsep := sepElt_of_ok l.pr u
  have hmem : ∀ P : (B.primes X).vT u, (B.primes X).piT u ∈ P.1.asIdeal := fun P => by
    have := hsep.conj P
    rwa [cO_cO] at this
  exact (GlobalTheory.Mem.Col2.AdT.sup_dual_eq_N ((I.stp u a i).rep c).1.1.deco.1 ((I.stp u a i).rep c).1.1.deco.2 _ hmem (l.pr.piT_cop u)).symm
