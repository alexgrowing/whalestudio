import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentNongenericQuotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericProdIrrOfGenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSingleNonzeroFactorEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.DiagCell

namespace GlobalTheory.CompanionTheory.CuspPairSub

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_singleton_of_sum' {ι A : Type*} [Fintype ι] [DecidableEq ι] {a : A} {t : ι → Multiset A}
    (h : ({a} : Multiset A) = ∑ j, t j) : ∃ j₀, t j₀ = {a} ∧ ∀ j, j ≠ j₀ → t j = 0 := by
  have hc : ∑ j, Multiset.card (t j) = 1 := by
    have := congrArg Multiset.card h
    rw [Multiset.card_sum] at this
    simpa using this.symm
  obtain ⟨j₀, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hc.symm ▸ one_ne_zero)
  have hz : ∀ j, j ≠ j₀ → t j = 0 := fun j hj => by
    have h2 := Finset.add_le_sum (s := Finset.univ) (f := fun j => Multiset.card (t j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j₀) (Finset.mem_univ j) (Ne.symm hj)
    simp only [hc] at h2
    exact Multiset.card_eq_zero.1 (by omega)
  refine ⟨j₀, ?_, hz⟩
  rw [h, Finset.sum_eq_single j₀ (fun j _ hj => hz j hj) (by simp)]

theorem eq_of_hasSupport_singleton {y z : IrrGL k} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun _ : Fin 1 => z.1) hd) _).1
    (piTensor fun _ => z.rep)
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := nonempty_equiv_of_isSubquotient hi z.2.rep.irr
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective))
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

theorem exists_equiv_of_cell {l : ℕ} (x y : Fin l → IrrGL k) (hxc : ∀ a, (x a).IsCusp)
    (hyp : ∀ a, 0 < (y a).1) (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1)
    (h0 : jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    ∃ e : Fin l ≃ Fin l, ∀ a, y a = x (e a) := by
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin l → Multiset (IrrGL k), (∀ j, HasSupport (s i j).ρ (t j)) ∧ {x i} = ∑ j, t j :=
    fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac hG hBZ (hasSupport_self (hxc i)) (f i)
      (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).rep (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b.1 i j = (y j).1 := by simpa using Fintype.card_congr (g j)
    have hy := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).2.rep.irr
      (hy.trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).2.rep.irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  choose r hr1 hr0 using fun i => exists_eq_singleton_of_sum' (hAt i)
  have hsurj : Function.Surjective r := by
    intro j
    by_contra hj
    push_neg at hj
    have hz : ∑ i, t i j = 0 := Finset.sum_eq_zero fun i _ => hr0 i j (Ne.symm (hj i))
    have h1 := (hC j).sum_fst
    rw [hz] at h1
    have := hyp j
    simp at h1
    omega
  have hbij : Function.Bijective r := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  let E := Equiv.ofBijective r hbij
  refine ⟨E.symm, fun j => ?_⟩
  have hrE : r (E.symm j) = j := E.apply_symm_apply j
  have hs1 : ∑ i, t i j = {x (E.symm j)} := by
    rw [Finset.sum_eq_single (E.symm j)]
    · rw [← hr1 (E.symm j), hrE]
    · intro i _ hi
      refine hr0 i j fun e => hi ?_
      exact hbij.1 (e.symm.trans hrE.symm)
    · simp
  have h2 := hC j
  rw [hs1] at h2
  exact eq_of_hasSupport_singleton h2

theorem exists_equiv_of_jm_ne_zero {l N : ℕ} (x y : Fin l → IrrGL k) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyp : ∀ a, 0 < (y a).1)
    (h : jm y hy (prodIrr x hx) ≠ 0) : ∃ e : Fin l ≃ Fin l, ∀ a, y a = x (e a) := by
  classical
  haveI : Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) := Fintype.ofFinite _
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (y j).2.rep
  let f : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1 :=
    fun b => b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1 :=
    fun b => b.nonempty_cols.some
  have h1 := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1.jhMult_eq (stdBlocks (fun a => (x a).1) hx)
    (stdBlocks (fun a => (y a).1) hy) (isSmooth_piTensor fun i => (x i).2.rep.smooth) f g hτ
  have h2 : jm y hy (prodIrr x hx) = jhMult (piTensor fun j => (y j).rep)
      (jac (stdBlocks (fun a => (y a).1) hy) (parInd (stdBlocks (fun a => (x a).1) hx)
        (piTensor fun i => (x i).rep))) := rfl
  rw [h2, h1] at h
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact exists_equiv_of_cell x y hxc hyp b (f b) (g b) hb

theorem jm_le_one (hA : IrreducibleAdmissibleGL) {l N : ℕ} (x y : Fin l → IrrGL k) (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp)
    (hinj : Function.Injective x) : jm y hy (prodIrr x hx) ≤ 1 := by
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA x y hx hy hxc hyc]
  have : Set.ncard {e : Fin l ≃ Fin l | ∀ a, y a = x (e a)} ≤ 1 := by
    refine (Set.ncard_le_one_iff (Set.toFinite _)).2 fun {e e'} he he' => Equiv.ext fun a => hinj ?_
    exact (he a).symm.trans (he' a)
  exact_mod_cast this

section Sat

variable {N : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y]
  [Module ℂ Y]

theorem false_of_sub_quot {h : ℕ} (t : Fin h → IrrGL k) (ht : ∑ a, (t a).1 = N) (hA : IrreducibleAdmissibleGL)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {ω : Representation ℂ (GL (Fin N) k) W}
    (f : ω.IntertwiningMap π) (hf : Function.Injective f) {τ : Representation ℂ (GL (Fin N) k) Y}
    (q : (GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π ω f).IntertwiningMap τ) (hq : Function.Surjective q)
    (hle : jm t ht π ≤ 1) (h1 : 1 ≤ jm t ht ω) (h2 : 1 ≤ jm t ht τ) : False := by
  let Q := GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π ω f
  let p : π.IntertwiningMap Q := ⟨(LinearMap.range f.toLinearMap).mkQ, fun g => by ext v; rfl⟩
  have hp : Function.Surjective p := Submodule.mkQ_surjective _
  have hex : Function.Exact f p := fun v => by
    show (LinearMap.range f.toLinearMap).mkQ v = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl
  have hadd : jm t ht π = jm t ht ω + jm t ht Q :=
    GlobalTheory.CompanionTheory.SocleJm.jhMult_jac_exact _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA t) f p hπ hf hp hex
  have hQs : IsSmooth Q := (IsSubquotient.of_surjective p hp).isSmooth hπ
  have h3 : jm t ht τ ≤ jm t ht Q :=
    GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient t ht τ Q hQs (.of_surjective q hq)
  have h4 : (1 : ℕ∞) + 1 ≤ 1 := calc
    (1 : ℕ∞) + 1 ≤ jm t ht ω + jm t ht Q := add_le_add h1 (h2.trans h3)
    _ = jm t ht π := hadd.symm
    _ ≤ 1 := hle
  exact absurd h4 (by norm_num)

theorem surjective_of_jm (hA : IrreducibleAdmissibleGL) {x y : IrrGL k} (hx : x.IsCusp) (hy : y.IsCusp) (hne : x ≠ y)
    (hd : ∑ a, (![x, y] a).1 = N) (hd' : ∑ a, (![y, x] a).1 = N) {ω : Representation ℂ (GL (Fin N) k) W}
    (f : ω.IntertwiningMap (prodIrr ![x, y] hd)) (hf : Function.Injective f)
    (h1 : 1 ≤ jm ![x, y] hd ω) (h2 : 1 ≤ jm ![y, x] hd' ω) : Function.Surjective f := by
  by_contra hns
  have hs := isSmooth_prodIrr ![x, y] hd
  have hxc : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hyc : ∀ a, (![y, x] a).IsCusp := Fin.forall_fin_two.2 ⟨hy, hx⟩
  have hinj : Function.Injective ![x, y] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hfl : HasFiniteLength (prodIrr ![x, y] hd) :=
    GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k 2 N
      (fun a => (![x, y] a).1) (fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (![x, y] a).2.rep) _
  let Q := GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep (prodIrr ![x, y] hd) ω f
  let p : (prodIrr ![x, y] hd).IntertwiningMap Q := ⟨(LinearMap.range f.toLinearMap).mkQ, fun g => by ext v; rfl⟩
  have hp : Function.Surjective p := Submodule.mkQ_surjective _
  have hQs : IsSmooth Q := (IsSubquotient.of_surjective p hp).isSmooth hs
  have hQn : Nontrivial (_ ⧸ LinearMap.range f.toLinearMap) :=
    Submodule.Quotient.nontrivial_iff.2 fun h => hns (LinearMap.range_eq_top.1 h)
  obtain ⟨Y', _, _, τ, hτs, hτi, q, hq⟩ := IrrQuot.exists_irreducible_smooth_quotient Q hQs
    (GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective p hp hfl) hQn
  have hτsub : IsSubquotient τ (prodIrr ![x, y] hd) := (IsSubquotient.of_surjective q hq).trans (.of_surjective p hp)
  have hsum : x.1 + y.1 = N := by simpa [Fin.sum_univ_two] using hd
  have hN : 0 < N := by have := hx.1; omega
  obtain ⟨u, hu, hu0, g, hg⟩ := GlobalTheory.CompanionTheory.JacquetLeft.exists_embedding hA τ hτs hτi hN
  haveI hYn : Nontrivial Y' := GlobalTheory.JacFactor.nontrivial_of_isIrreducible hτi
  have hg0 : ∃ v, g v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Y')
    exact ⟨v, fun h => hv (hg (h.trans (map_zero g).symm))⟩
  have hj := GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA u hu τ hτs g hg0
  have hj' := GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient u hu τ _ hs hτsub
  by_cases hz : (u 1).1 = 0
  · obtain ⟨z, hz1, ⟨E⟩⟩ := GlobalTheory.CompanionTheory.FineProd.ProdSingle.prodIrr_single u hu 0 (fun i hi => by
      obtain rfl : i = 1 := by omega
      exact hz)
    have hsq : IsSubquotient τ z.rep.ρ :=
      .of_injective (E.toIntertwiningMap.comp g) (E.toLinearEquiv.injective.comp hg)
    obtain ⟨θ⟩ := nonempty_equiv_of_isSubquotient hτi z.rep.irr hsq
    have hc : IrrGL.IsCusp (⟨N, z⟩ : IrrGL k) := hz1 ▸ hu0
    have h0 := GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp hA ⟨N, z⟩ ![x, y] hd hc le_rfl
      (Fin.forall_fin_two.2 ⟨hx.1, hy.1⟩)
    exact jhMult_ne_zero_iff.2 ((IsSubquotient.of_injective θ.toIntertwiningMap θ.toLinearEquiv.injective).trans hτsub) h0
  · have hpos : ∀ a, 0 < (u a).1 := by
      refine Fin.forall_fin_two.2 ⟨hu0.1, Nat.pos_of_ne_zero hz⟩
    obtain ⟨e, he⟩ := exists_equiv_of_jm_ne_zero ![x, y] u hd hu hxc hpos
      (ENat.one_le_iff_ne_zero.1 (hj.trans hj'))
    have hcases : u = ![x, y] ∨ u = ![y, x] := by
      have hee : e 0 ≠ e 1 := fun h => by simpa using e.injective h
      have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
      rcases key _ _ hee with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
      · exact Or.inr (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
    rcases hcases with rfl | rfl
    · exact false_of_sub_quot ![x, y] hd hA hs f hf q hq (jm_le_one hA _ _ hd hd hxc hxc hinj) h1 hj
    · exact false_of_sub_quot ![y, x] hd' hA hs f hf q hq (jm_le_one hA _ _ hd hd' hxc hyc hinj) h2 hj

end Sat

theorem isGeneric_of_injective {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ω : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W} (hω : IsSmooth ω) (hσ : IsSmooth σ)
    (g : ω.IntertwiningMap σ) (hg : Function.Injective g) (h : IsGeneric ω) : IsGeneric σ := by
  obtain ⟨ψ, hc, h1, h2⟩ := h
  refine ⟨ψ, hc, h1, ?_⟩
  unfold IsGenericFor at h2 ⊢
  obtain ⟨q, hq⟩ := exists_ne (0 : TwJacquet ω (unipB k (Fin N)) (whitChar ψ N))
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hw : w ∉ twKer ω (unipB k (Fin N)) (whitChar ψ N) := fun h => hq ((Submodule.Quotient.mk_eq_zero _).2 h)
  have hgw : g w ∉ twKer σ (unipB k (Fin N)) (whitChar ψ N) := fun h =>
    hw (GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hc N ω σ hω hσ g.toLinearMap hg
      (fun a v => Representation.IntertwiningMap.isIntertwining _ _ g a v) w h)
  exact ⟨Submodule.Quotient.mk (g w), 0, fun h => hgw ((Submodule.Quotient.mk_eq_zero _).1 h)⟩

theorem nu_one_ne {x : IrrGL k} (hx : 0 < x.1) : x.nu 1 ≠ x := fun h => by
  have h1 : x.nu ((1 : ℕ) : ℂ) = x.nu ((0 : ℕ) : ℂ) := by simpa using h
  exact one_ne_zero (IrrGL.nu_natCast_inj hx |>.1 h1)

theorem isGeneric_prodIrr (hCG : GlobalTheory.BZSeg.CuspGeneric k) {x y : IrrGL k} (hx : x.IsCusp) (hy : y.IsCusp) {N : ℕ}
    (hd : ∑ a, (![x, y] a).1 = N) : IsGeneric (prodIrr ![x, y] hd) := by
  have hG := GlobalTheory.CompanionTheory.BZMir.genericProdIrr_of_genericProdIff k
    (GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity k (GlobalTheory.CompanionTheory.Rodier.whitHeredity k))
  have hc : ∀ z : IrrGL k, z.IsCusp → IsGeneric z.rep := fun z hz =>
    hCG z.1 _ z.rep hz.1 z.2.rep.smooth z.2.rep.irr hz.2
  exact (hG 2 N ![x, y] hd).2 (Fin.forall_fin_two.2 ⟨hc x hx, hc y hy⟩)

theorem cuspPairSubGeneric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.BZSeg.NuPair k →
    GlobalTheory.BZSeg.CuspGeneric k → GlobalTheory.BZSeg.CuspPairSubGeneric k := by
  intro k _ _ _ _ hA _ hNu hCG x y N hd hx hy hne W _ _ σ f hf hW
  have hs := isSmooth_prodIrr ![x, y] hd
  have hsq := IsSubquotient.of_injective f hf
  have hσs := hsq.isSmooth hs
  have hfl : HasFiniteLength (prodIrr ![x, y] hd) :=
    GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k 2 N
      (fun a => (![x, y] a).1) (fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (![x, y] a).2.rep) _
  obtain ⟨S, g, hg⟩ := GlobalTheory.CompanionTheory.IrrSub.exists_irrRep_injective k N W _ σ (prodIrr ![x, y] hd) hσs hW hsq hfl
  refine isGeneric_of_injective S.smooth hσs g hg ?_
  by_contra hng
  obtain ⟨α, β, β', hd1, hd2, hα, hβ, hββ, h1, h2⟩ := hNu N S.V S.ρ S.smooth S.irr hng
  let ι : S.ρ.IntertwiningMap (prodIrr ![x, y] hd) := f.comp g
  have hι : Function.Injective ι := hf.comp hg
  haveI : Nontrivial S.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible S.irr
  have hι0 : ∃ v, ι v ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : S.V)
    exact ⟨v, fun h => hv (hι (h.trans (map_zero ι).symm))⟩
  have hF : 1 ≤ jm ![x, y] hd S.ρ := GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA _ hd S.ρ S.smooth ι hι0
  have hxc : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have key : ∀ (u : Fin 2 → IrrGL k) (hu : ∑ a, (u a).1 = N), (∀ a, 0 < (u a).1) → 1 ≤ jm u hu S.ρ →
      u = ![x, y] ∨ u = ![y, x] := by
    intro u hu hpos hj
    have hj' := GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient u hu S.ρ _ hs (.of_injective ι hι)
    obtain ⟨e, he⟩ := exists_equiv_of_jm_ne_zero ![x, y] u hd hu hxc hpos
      (ENat.one_le_iff_ne_zero.1 (hj.trans hj'))
    have hee : e 0 ≠ e 1 := fun h => by simpa using e.injective h
    have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
    rcases key _ _ hee with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
    · exact Or.inr (funext (Fin.forall_fin_two.2 ⟨(he 0).trans (by simp [a]), (he 1).trans (by simp [b])⟩))
  have hp1 : ∀ a, 0 < (![α, β] a).1 := Fin.forall_fin_two.2 ⟨hα, hβ⟩
  have hp2 : ∀ a, 0 < (![β', α.nu 1] a).1 := Fin.forall_fin_two.2 ⟨hββ ▸ hβ, hα⟩
  have c1 := key _ hd1 hp1 h1
  have c2 := key _ hd2 hp2 h2
  have e0 : ∀ {a b c d : IrrGL k}, ![a, b] = ![c, d] → a = c ∧ b = d := fun h =>
    ⟨congrFun h 0, congrFun h 1⟩
  rcases c1 with c1 | c1 <;> obtain ⟨rfl, rfl⟩ := e0 c1
  · rcases c2 with c2 | c2 <;> obtain ⟨-, h3⟩ := e0 c2
    · exact hne h3.symm
    · exact nu_one_ne hx.1 h3
  · rcases c2 with c2 | c2 <;> obtain ⟨-, h3⟩ := e0 c2
    · exact nu_one_ne hy.1 h3
    · have hxy : β ≠ α := fun h => nu_one_ne hy.1 (h3.trans h)
      have hsurj : Function.Surjective ι := surjective_of_jm hA hx hy hxy hd hd1 ι hι hF h1
      exact hng (GlobalTheory.CompanionTheory.BZSeg.isGeneric_of_surjective ι hsurj (isGeneric_prodIrr hCG hx hy hd))

end GlobalTheory.CompanionTheory.CuspPairSub
end
