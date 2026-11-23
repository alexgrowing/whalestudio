import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.IntSpanCmp

open MvPolynomial

variable {σ : Type}

def spanO {K : Type} [CommRing K] (O : Set K) (G : Set (MvPolynomial σ ℤ)) :
    AddSubgroup (MvPolynomial σ K) :=
  AddSubgroup.closure {p | ∃ r ∈ O, ∃ g ∈ G, p = r • map (Int.castRingHom K) g}

theorem exists_fin_of_mem {K : Type} [CommRing K] {O : Set K} (hO : ∀ r ∈ O, -r ∈ O)
    {G : Set (MvPolynomial σ ℤ)} {P : MvPolynomial σ K} (h : P ∈ spanO O G) :
    ∃ (m : ℕ) (r : Fin m → K) (g : Fin m → MvPolynomial σ ℤ), (∀ i, r i ∈ O ∧ g i ∈ G) ∧
      P = ∑ i, r i • map (Int.castRingHom K) (g i) := by
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, hr, g, hg, rfl⟩ := hx
    exact ⟨1, fun _ => r, fun _ => g, fun _ => ⟨hr, hg⟩, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, r1, g1, h1, rfl⟩ := hx
    obtain ⟨m2, r2, g2, h2, rfl⟩ := hy
    refine ⟨m1 + m2, Fin.append r1 r2, Fin.append g1 g2, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using h1 j
      · simpa using h2 j
    · rw [Fin.sum_univ_add]; simp
  | neg x _ hx =>
    obtain ⟨m, r, g, h, rfl⟩ := hx
    exact ⟨m, fun i => -r i, g, fun i => ⟨hO _ (h i).1, (h i).2⟩, by simp [Finset.sum_neg_distrib, neg_smul]⟩

theorem map_map_int {L K : Type} [CommRing L] [CommRing K] (φ : L →+* K) (g : MvPolynomial σ ℤ) :
    map φ (map (Int.castRingHom L) g) = map (Int.castRingHom K) g := by
  rw [MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom L)) (Int.castRingHom K)]

theorem map_smul_map {L K : Type} [CommRing L] [CommRing K] (φ : L →+* K) (r : L) (g : MvPolynomial σ ℤ) :
    map φ (r • map (Int.castRingHom L) g) = φ r • map (Int.castRingHom K) g := by
  rw [smul_eq_C_mul, map_mul, map_C, map_map_int, smul_eq_C_mul]

theorem smul_map_mem {K : Type} [CommRing K] (O : AddSubgroup K) (G : Set (MvPolynomial σ ℤ))
    {r : K} (hr : r ∈ O) {g : MvPolynomial σ ℤ} (hg : g ∈ Submodule.span ℤ G) :
    r • map (Int.castRingHom K) g ∈ spanO (O : Set K) G := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact AddSubgroup.subset_closure ⟨r, hr, x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | smul z x _ hx =>
    rw [map_zsmul, smul_comm]
    exact zsmul_mem hx z

theorem map_mem {L K : Type} [CommRing L] [CommRing K] (φ : L →+* K) {O : Set L} {O' : Set K}
    (h : ∀ r ∈ O, φ r ∈ O') {G : Set (MvPolynomial σ ℤ)} {R : MvPolynomial σ L} (hR : R ∈ spanO O G) :
    map φ R ∈ spanO O' G := by
  induction hR using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, hr, g, hg, rfl⟩ := hx
    rw [map_smul_map]
    exact AddSubgroup.subset_closure ⟨φ r, h r hr, g, hg, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem of_map_mem {L K : Type} [CommRing L] [CommRing K] (φ : L →+* K) (hφ : Function.Injective φ)
    (O : AddSubgroup L) {G : Set (MvPolynomial σ ℤ)} {R : MvPolynomial σ L}
    (hR : map φ R ∈ spanO (φ '' (O : Set L)) G) : R ∈ spanO (O : Set L) G := by
  obtain ⟨m, r, g, h, hR'⟩ := exists_fin_of_mem
    (fun x hx => by obtain ⟨y, hy, e⟩ := hx; exact ⟨-y, neg_mem hy, by rw [map_neg, e]⟩) hR
  choose r' hr' e using fun i => (h i).1
  have : R = ∑ i, r' i • map (Int.castRingHom L) (g i) := by
    apply map_injective φ hφ
    rw [hR', map_sum]
    simp only [map_smul_map, e]
  rw [this]
  exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨r' i, hr' i, g i, (h i).2, rfl⟩

theorem li_map {ι K : Type} [Field K] [Module.Flat ℤ K] {e : ι → MvPolynomial σ ℤ}
    (he : LinearIndependent ℤ e) : LinearIndependent K (fun k => map (Int.castRingHom K) (e k)) := by
  have h1 := Module.Flat.linearIndependent_one_tmul (S := K) he
  have h2 := h1.map' (algebraTensorAlgEquiv ℤ K).toLinearEquiv.toLinearMap (LinearEquiv.ker _)
  have key : ((algebraTensorAlgEquiv ℤ K).toLinearEquiv.toLinearMap ∘ fun x => (1 : K) ⊗ₜ[ℤ] e x) =
      fun k => map (Int.castRingHom K) (e k) := by
    funext k
    simp [algebraTensorAlgEquiv_tmul]
  rw [key] at h2
  exact h2

end GlobalTheory.IntSpanCmp

end

namespace GlobalTheory.IntSpanCmp

open MvPolynomial

variable {σ : Type}

theorem keyCoord {L K : Type} [Field L] [Field K] [Module.Flat ℤ K] (ψ : L →+* K) (Oc : AddSubgroup K)
    (G : Set (MvPolynomial σ ℤ)) (R : MvPolynomial σ L) (hR : R ∈ spanO (Set.univ : Set L) G)
    (hc : map ψ R ∈ spanO (Oc : Set K) G) :
    R ∈ spanO ((Oc.comap ψ.toAddMonoidHom : AddSubgroup L) : Set L) G := by
  classical
  obtain ⟨m1, r1, g1, h1, hR1⟩ := exists_fin_of_mem (O := (Set.univ : Set L)) (fun _ _ => Set.mem_univ _) hR
  obtain ⟨m2, r2, g2, h2, hR2⟩ := exists_fin_of_mem (fun _ h => neg_mem h) hc
  set T : Finset (MvPolynomial σ ℤ) := Finset.univ.image g1 ∪ Finset.univ.image g2 with hT
  set N : Submodule ℤ (MvPolynomial σ ℤ) := Submodule.span ℤ (T : Set (MvPolynomial σ ℤ)) with hN
  haveI : Module.Finite ℤ N := Module.Finite.span_of_finite ℤ T.finite_toSet
  haveI : Module.Free ℤ N := Module.free_of_finite_type_torsion_free'
  set b := Module.Free.chooseBasis ℤ N with hb
  set e : Module.Free.ChooseBasisIndex ℤ N → MvPolynomial σ ℤ := fun k => (b k : MvPolynomial σ ℤ) with he_def
  have he : LinearIndependent ℤ e := b.linearIndependent.map' N.subtype N.ker_subtype
  let crd : MvPolynomial σ ℤ → Module.Free.ChooseBasisIndex ℤ N → ℤ :=
    fun g => if hg : g ∈ N then b.repr ⟨g, hg⟩ else 0
  have hexp : ∀ g ∈ N, g = ∑ k, crd g k • e k := by
    intro g hg
    have := congrArg Subtype.val (b.sum_repr ⟨g, hg⟩)
    rw [Submodule.coe_sum] at this
    simp only [SetLike.val_smul] at this
    simp only [crd, dif_pos hg, e]
    exact this.symm
  have mapExp : ∀ (K' : Type) [CommRing K'], ∀ g ∈ N,
      map (Int.castRingHom K') g = ∑ k, (crd g k : K') • map (Int.castRingHom K') (e k) := by
    intro K' _ g hg
    conv_lhs => rw [hexp g hg]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hg1 : ∀ i, g1 i ∈ N := fun i => Submodule.subset_span (by simp [hT])
  have hg2 : ∀ i, g2 i ∈ N := fun i => Submodule.subset_span (by simp [hT])
  have hNG : N ≤ Submodule.span ℤ G := by
    rw [hN, Submodule.span_le]
    intro g hg
    simp only [hT, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
      Set.mem_range] at hg
    rcases hg with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Submodule.subset_span (h1 i).2
    · exact Submodule.subset_span (h2 i).2
  set c : Module.Free.ChooseBasisIndex ℤ N → L := fun k => ∑ i, r1 i * (crd (g1 i) k : L) with hc_def
  set d : Module.Free.ChooseBasisIndex ℤ N → K := fun k => ∑ i, r2 i * (crd (g2 i) k : K) with hd_def
  have hRc : R = ∑ k, c k • map (Int.castRingHom L) (e k) := by
    rw [hR1]
    simp_rw [mapExp L _ (hg1 _), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp [c, Finset.sum_smul]
  have hψ : map ψ R = ∑ k, ψ (c k) • map (Int.castRingHom K) (e k) := by
    rw [hRc, map_sum]; simp only [map_smul_map]
  have hd : map ψ R = ∑ k, d k • map (Int.castRingHom K) (e k) := by
    rw [hR2]
    simp_rw [mapExp K _ (hg2 _), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp [d, Finset.sum_smul]
  have hcd : ∀ k, ψ (c k) = d k := by
    have := Fintype.linearIndependent_iff.mp (li_map (K := K) he) (fun k => ψ (c k) - d k)
      (by simp only [sub_smul, Finset.sum_sub_distrib]; rw [← hψ, ← hd, sub_self])
    exact fun k => sub_eq_zero.mp (this k)
  have hdO : ∀ k, d k ∈ Oc := fun k =>
    sum_mem fun i _ => by
      rw [mul_comm, ← zsmul_eq_mul]
      exact zsmul_mem (h2 i).1 _
  rw [hRc]
  refine sum_mem fun k _ => smul_map_mem _ G ?_ (hNG (b k).2)
  show ψ (c k) ∈ Oc
  rw [hcd]; exact hdO k

end GlobalTheory.IntSpanCmp

namespace GlobalTheory.IntSpanCmp

open MvPolynomial

theorem ten_map {ι R K : Type} [Fintype ι] [CommRing R] [CommRing K] (φ : R →+* K) {n : ℕ}
    (f : ι → MvPolynomial (Fin n × Fin n) R) :
    Formalism.L2.Forms.ten (fun τ => map φ (f τ)) = map φ (Formalism.L2.Forms.ten f) := by
  simp [Formalism.L2.Forms.ten, map_prod, map_rename]

def ballO (p : ℕ) [Fact p.Prime] : AddSubgroup ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [norm_neg] using ha

noncomputable def polFunHom {K ι : Type} [CommRing K] (n : ℕ) :
    MvPolynomial (ι × Fin n × Fin n) K →+ ((ι → Matrix (Fin n) (Fin n) K) → K) where
  toFun := polFun
  map_zero' := by funext y; simp [polFun]
  map_add' P Q := by funext y; simp [polFun]

theorem polFunHom_inj {K ι : Type} [Field K] [Infinite K] (n : ℕ) :
    Function.Injective (polFunHom (K := K) (ι := ι) n) := by
  intro P Q h
  apply MvPolynomial.funext
  intro x
  have := congrFun h (fun τ a b => x (τ, a, b))
  exact this

theorem polFun_smul_ten {K ι : Type} [CommRing K] [Fintype ι] {n : ℕ} (r : K)
    (f : ι → MvPolynomial (Fin n × Fin n) ℤ) :
    polFun (r • map (Int.castRingHom K) (Formalism.L2.Forms.ten f)) =
      fun y => r * ∏ τ, eval (fun k : Fin n × Fin n => y τ k.1 k.2) (map (Int.castRingHom K) (f τ)) := by
  funext y
  simp [polFun, Formalism.L2.Forms.ten, smul_eq_C_mul, map_prod, eval_prod, eval_rename, Function.comp_def, map_rename]

end GlobalTheory.IntSpanCmp

namespace GlobalTheory.IntSpanCmp

open MvPolynomial

theorem intSpan_iff_delW : ∀ (D : D7) (Pl : Examples₂.EntPl D) (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (R : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL),
    MvPolynomial.map D.what₂.embLL R ∈ Formalism.L2.Forms.RatSpan D lam →
    (MvPolynomial.map D.what₂.embLL R ∈ Formalism.L2.Forms.IntSpan D w lam ↔
      polFun (MvPolynomial.map (Pl.iL w) R) ∈ WeylLatticeDuality.DelW (D.what₂.places.resChar w) D.what₂.Tau n (fun τ => (lam τ).natW)) := by
  intro D Pl w n lam R hRat
  classical
  set G : Set (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℤ) :=
    {g | ∃ f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ, (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
      g = Formalism.L2.Forms.ten f} with hG
  have hinj : Function.Injective D.what₂.embLL := D.what₂.embLL.injective
  have hR : R ∈ spanO (Set.univ : Set D.what₂.LL) G := by
    have h1 : MvPolynomial.map D.what₂.embLL R ∈
        spanO (D.what₂.embLL '' ((⊤ : AddSubgroup D.what₂.LL) : Set D.what₂.LL)) G := by
      refine (AddSubgroup.closure_le _).mpr ?_ hRat
      rintro p ⟨r, f, hf, rfl⟩
      exact AddSubgroup.subset_closure
        ⟨D.what₂.embLL r, ⟨r, trivial, rfl⟩, Formalism.L2.Forms.ten f, ⟨f, hf, rfl⟩, by rw [ten_map]⟩
    have := of_map_mem D.what₂.embLL hinj ⊤ h1
    simpa using this
  have hInt : MvPolynomial.map D.what₂.embLL R ∈ Formalism.L2.Forms.IntSpan D w lam ↔
      R ∈ spanO (((intW D.what₂.places w).toAddSubgroup : AddSubgroup D.what₂.LL) : Set D.what₂.LL) G := by
    constructor
    · intro h
      have h1 : MvPolynomial.map D.what₂.embLL R ∈ spanO (D.what₂.embLL ''
          (((intW D.what₂.places w).toAddSubgroup : AddSubgroup D.what₂.LL) : Set D.what₂.LL)) G := by
        refine (AddSubgroup.closure_le _).mpr ?_ h
        rintro p ⟨r, f, hr, hf, rfl⟩
        exact AddSubgroup.subset_closure
          ⟨D.what₂.embLL r, ⟨r, hr, rfl⟩, Formalism.L2.Forms.ten f, ⟨f, hf, rfl⟩, by rw [ten_map]⟩
      exact of_map_mem D.what₂.embLL hinj (intW D.what₂.places w).toAddSubgroup h1
    · intro h
      have h1 := map_mem D.what₂.embLL (O' := D.what₂.embLL ''
        (((intW D.what₂.places w).toAddSubgroup : AddSubgroup D.what₂.LL) : Set D.what₂.LL))
        (fun r hr => ⟨r, hr, rfl⟩) h
      refine (AddSubgroup.closure_le _).mpr ?_ h1
      rintro p ⟨_, ⟨r, hr, rfl⟩, g, ⟨f, hf, rfl⟩, rfl⟩
      exact AddSubgroup.subset_closure ⟨r, f, Subring.mem_toAddSubgroup.mp hr, hf, by rw [ten_map]⟩
  have hDelW : WeylLatticeDuality.DelW (D.what₂.places.resChar w) D.what₂.Tau n (fun τ => (lam τ).natW) =
      (spanO ((ballO (D.what₂.places.resChar w) : AddSubgroup ℂ_[D.what₂.places.resChar w]) :
        Set ℂ_[D.what₂.places.resChar w]) G).map (polFunHom n) := by
    unfold WeylLatticeDuality.DelW
    rw [spanO, AddMonoidHom.map_closure]
    refine congrArg AddSubgroup.closure ?_
    ext F
    constructor
    · rintro ⟨r, f, hr, hf, rfl⟩
      exact ⟨_, ⟨r, hr, Formalism.L2.Forms.ten f, ⟨f, hf, rfl⟩, rfl⟩, by simp [polFunHom, polFun_smul_ten]⟩
    · rintro ⟨_, ⟨r, hr, _, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
      exact ⟨r, f, hr, hf, by simp [polFunHom, polFun_smul_ten]⟩
  have hD : polFun (MvPolynomial.map (Pl.iL w) R) ∈
      WeylLatticeDuality.DelW (D.what₂.places.resChar w) D.what₂.Tau n (fun τ => (lam τ).natW) ↔
      MvPolynomial.map (Pl.iL w) R ∈ spanO ((ballO (D.what₂.places.resChar w) :
        AddSubgroup ℂ_[D.what₂.places.resChar w]) : Set ℂ_[D.what₂.places.resChar w]) G := by
    rw [hDelW]
    exact AddSubgroup.mem_map_iff_mem (polFunHom_inj n)
  rw [hInt, hD]
  constructor
  · intro h
    exact map_mem (Pl.iL w) (fun r hr => (Pl.iL_int w r).1 hr) h
  · intro h
    have := keyCoord (Pl.iL w) (ballO (D.what₂.places.resChar w)) G R hR h
    have hset : (((ballO (D.what₂.places.resChar w)).comap (Pl.iL w).toAddMonoidHom :
        AddSubgroup D.what₂.LL) : Set D.what₂.LL) =
        (((intW D.what₂.places w).toAddSubgroup : AddSubgroup D.what₂.LL) : Set D.what₂.LL) := by
      ext x
      rw [SetLike.mem_coe, SetLike.mem_coe, Subring.mem_toAddSubgroup]
      exact (Pl.iL_int w x).symm
    rw [hset] at this
    exact this

end GlobalTheory.IntSpanCmp
