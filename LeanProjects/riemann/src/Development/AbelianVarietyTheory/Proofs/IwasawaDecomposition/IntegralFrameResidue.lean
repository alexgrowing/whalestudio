import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombinationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFrameValuationBoundStatement
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HTLine.GenInd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem embK_mem {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (τ : E →+* ℂ) (a : 𝓞 E) :
    embK c τ a ∈ c.V W := by
  show ((embK c τ a : c.F) : ℂ) ∈ W
  rw [embK_coe]
  have h1 : IsIntegral ℤ (τ (a : E)) := (NumberField.RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom
  have h2 : IsIntegral W (τ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

theorem natCast_mem_max {l : Level H} (c : Coeff l) {W : ValuationSubring ℂ} {p : ℕ} (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.V W) ∈ IsLocalRing.maximalIdeal (c.V W) := by
  obtain ⟨h0, h1⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 hW
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
  intro hu
  let g : c.V W →+* W := (c.F.val.toRingHom.comp (c.V W).subtype).codRestrict W (fun x => x.2)
  apply h1
  have := hu.map g
  rw [map_natCast] at this
  convert this using 1
  exact Subtype.ext (by simp)

theorem exists_ext {F : Type} [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ)
    (hp : (p : V) ∈ IsLocalRing.maximalIdeal V) {k : Type} [Field k] (g : V →+* k) (hk : (p : k) ≠ 0) :
    ∃ f : F →+* k, ∀ v : V, f v = g v := by
  have hker : RingHom.ker g = ⊥ := by
    by_contra h
    have hm : (RingHom.ker g).IsMaximal := Ideal.IsPrime.isMaximal (RingHom.ker_isPrime g) h
    have he := IsLocalRing.eq_maximalIdeal hm
    apply hk
    have : (p : V) ∈ RingHom.ker g := he ▸ hp
    simpa using this
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun x hx => by
    have : x ∈ RingHom.ker g := hx
    rwa [hker] at this
  exact ⟨IsFractionRing.lift hinj, fun v => IsFractionRing.lift_algebraMap (K := F) hinj v⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem dualMap_epsMul {R k : Type} [CommRing R] [CommRing k] (ψ : R →+* k) (r : R) :
    (dualMap ψ).comp (epsMul r) = (epsMul (ψ r)).comp (dualMap ψ) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul]
  · simp [dualMap, epsMul, mul_comm]

variable {X : Scheme.{0}} {t : SAB H X}

theorem ind_of_basis {R k : Type} [CommRing R] [Field k] {x : Sp R ⟶ X} {n m : ℕ}
    {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hv : GlobalTheory.LineNorm.IsTanBasis t x v) (e : Fin m ↪ Fin n)
    (ψ : R →+* k) : Pull.Ind t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ v (e i)) := by
  classical
  have hT : ∀ j, IsTanAtG t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v j) := fun j => GlobalTheory.LieMet.isTan_map ψ rfl (hv.1 j)
  refine ⟨fun i => hT (e i), fun cf cf' w h h' => ?_⟩
  let V : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap ψ ≫ x) t.G := fun j => GlobalTheory.LieMet.tanOf (hT j)
  have hs : ∀ d : Fin m → k, ∑ j, Function.extend e d 0 j • V j = ∑ i, d i • V (e i) := fun d => by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun j _ hj => by
      rw [Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => hj (Finset.mem_map.2 ⟨i, Finset.mem_univ _, hi⟩)),
        Pi.zero_apply, zero_smul]), Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by rw [e.injective.extend_apply]
  have hc : ∀ d, IsCombAtG t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ v (e i)) d w →
      IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (Function.extend e d 0) w := fun d hd => by
    have h1 := (Pull.comb_iff (fun i => V (e i)) d w).1 hd
    exact (Pull.comb_iff V _ w).2 (by rw [hs]; exact h1)
  have hw : IsTanAtG t (spMap ψ ≫ x) w := by
    rw [(Pull.comb_iff (fun i => V (e i)) cf w).1 h]; exact GlobalTheory.LieMet.isTan_tv _
  have := (hv.2 k ψ w hw).unique (hc cf h) (hc cf' h')
  funext i
  have h2 := congrFun this (e i)
  rwa [e.injective.extend_apply, e.injective.extend_apply] at h2

theorem ind_concat {Dw : Datum H} {l : Level H} (c : Coeff l) {k : Type} [Field k] (f : c.F →+* k) {x : Sp k ⟶ X}
    (u : Vecs Dw t k) (hE : ∀ τ i (a : 𝓞 E), u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i)
    (hI : ∀ τ, Pull.Ind t x (u τ)) :
    Pull.Ind t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) := by
  classical
  refine ⟨fun i => (hI _).1 _, fun cf cf' w h h' => ?_⟩
  let _ : Algebra c.F k := f.toAlgebra
  let U : (y : GlobalTheory.ShFam.Pad.Letter Dw) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G := fun y => GlobalTheory.LieMet.tanOf ((hI y.1).1 y.2)
  let e := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have hc : ∀ cf w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
      cf w ↔ w = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (∑ y, cf (e.symm y) • U y)).left := fun cf w => by
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    exact GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun i => U (e i)) cf w
  have hτ : ∀ τ cf w, IsCombAtG t x (u τ) cf w ↔ w = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (∑ i, cf i • U ⟨τ, i⟩)).left :=
    fun τ cf w => GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun i => U ⟨τ, i⟩) cf w
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := k) t.act
  have hEv : ∀ τ (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) v ↔ ∀ a : 𝓞 E,
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ (t.act.act a).left =
        spMap (epsMul (f (embK c τ a))) ≫ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left := fun τ v =>
    forall_congr' fun a => ⟨fun h => congrArg (fun z => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv z).left) h,
      fun h => GlobalTheory.LieMet.tan_ext h⟩
  have hS : ∀ τ (a : Fin (Dw.mult τ) → k), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) (∑ i, a i • U ⟨τ, i⟩) :=
    fun τ a s => by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hEv τ (U ⟨τ, i⟩)).2 (hE τ i) s, smul_comm]
  have h1 := GlobalTheory.LieMet.tan_ext (((hc cf w).1 h).symm.trans ((hc cf' w).1 h'))
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
  funext i
  obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective i
  have h2 := congrArg (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ) h1
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _),
    ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _)] at h2
  exact congrFun ((hI τ).2 _ _ _ ((hτ τ _ _).2 rfl)
    ((hτ τ _ _).2 (congrArg (fun z => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv z).left) h2))) i

end GlobalTheory.HTLine.GenInd

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.HTLine.GenInd.ind_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (k : Type) [Field k] (ψ : Γ(Z.X, U) →+* k), (p : k) ≠ 0 → (∀ τ, Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (w.bc ψ τ)) ∧ Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (fun i : Fin (letters Dw).length => w.bc ψ ((letters Dw).get i).1 ((letters Dw).get i).2) := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z U hU w hw k _ ψ hk
  obtain ⟨b, hb⟩ : ∃ b : Z.i.c.V W →+* Γ(Z.X, U), hU.fromSpec ≫ Z.s = spMap b := by
    refine ⟨(Spec.preimage (hU.fromSpec ≫ Z.s)).hom, ?_⟩
    exact (Spec.map_preimage (hU.fromSpec ≫ Z.s)).symm
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff (W := W) Z.i.c hp.ne_zero hW
  obtain ⟨f, hf⟩ := GlobalTheory.HTLine.GenInd.exists_ext (Z.i.c.V W) p (GlobalTheory.HTLine.GenInd.natCast_mem_max Z.i.c hW) (ψ.comp b) hk
  have hE : ∀ τ i (a : 𝓞 E), w.bc ψ τ i ≫ ((Y Z.i).t.act.act a).left =
      spMap (epsMul (f (embK Z.i.c τ a))) ≫ w.bc ψ τ i := by
    intro τ i a
    have h := GlobalTheory.HTLine.GenInd.embK_mem Z.i.c W τ a
    have h1 := GlobalTheory.T.integral_frame_valuation_bound E H Dw Xo p W Y i₀ Z U hU w hw b hb τ i a h
    have h2 : f (embK Z.i.c τ a) = ψ (b ⟨_, h⟩) := hf ⟨_, h⟩
    show spMap (dualMap ψ) ≫ w τ i ≫ _ = spMap (epsMul _) ≫ spMap (dualMap ψ) ≫ w τ i
    rw [h1, h2, ← Category.assoc, ← Category.assoc, GlobalTheory.HTLine.GenInd.spMap_comp',
      GlobalTheory.HTLine.GenInd.spMap_comp', GlobalTheory.HTLine.GenInd.dualMap_epsMul]
  have hI : ∀ τ, Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (w.bc ψ τ) := by
    intro τ
    obtain ⟨n, v, e, hve, hvt, hvu⟩ := hw.1 τ
    have hB := GlobalTheory.T.isTanBasis_of_unique_combination E H _ (Y Z.i).t _ (hU.fromSpec ≫ Z.π) n v hvt hvu
    have h3 := GlobalTheory.HTLine.GenInd.ind_of_basis hB e ψ
    simp only [hve] at h3
    exact h3
  refine ⟨hI, ?_⟩
  exact GlobalTheory.HTLine.GenInd.ind_concat (t := (Y Z.i).t) (x := spMap ψ ≫ hU.fromSpec ≫ Z.π) (Dw := Dw) Z.i.c f (w.bc ψ) hE hI
