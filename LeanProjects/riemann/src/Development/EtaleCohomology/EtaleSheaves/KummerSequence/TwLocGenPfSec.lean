import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPfSec

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  exact h.symm

def TwSecLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
  Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (hQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W h => Q W (h ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, h, g, hg, hh, rfl⟩
  exact hT' V g hg W h hh

theorem loc_surj {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : Sec (ofRings R M) U) :
    Loc U fun V g => ∃ x : M.obj Γ(V, ⊤), Sec.res g y = ofRings.sec M V x := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y
  refine ⟨_, h, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, hx.symm⟩

end LateralTheory.E.H2CurveOrder.TwLocGenPfSec

namespace LateralTheory.E.H2CurveOrder.TwLocGenPfSec

def ZarPow : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)),
  Loc V fun W h => ∃ a : (ZMod q)ˣ, (ξ.map h.appTop.hom).1 = (ζ.map h.appTop.hom).1 ^ (a : ZMod q).val

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

theorem twF_loc (hZ : ZarPow) (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤))
    (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction f using Finsupp.induction with
  | zero =>
    refine loc_mono (loc_true V) fun W h _ => ⟨0, ?_⟩
    rw [zero_smul, Submodule.Quotient.mk_zero]
    exact map_zero ((twF q i).map h.appTop).hom
  | single_add ξ b g _ _ ih =>
    refine loc_mono (loc_and (hZ q V ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
      ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
    rw [Submodule.Quotient.mk_add]
    refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
    rw [hc, twF_map_mk, Finsupp.mapDomain_single,
      twF_single_pow q i _ _ _ a ha b, add_smul]
    rfl

theorem TwSecLoc_of (hZ : ZarPow) : LateralTheory.E.H2CurveOrder.TwLocGenPfSec.TwSecLoc := by
  intro q _ i U ζ y
  refine loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_
  refine loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  have e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
    apply Subtype.ext
    simp [Prim.map]
    rfl
  rw [e]
  refine (congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_
  refine (LateralTheory.E.H2CurveOrder.TwLocGenPfSec.ofRings_sec_res (twF q i) h x).trans ?_
  rw [hc, ← hp]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

end LateralTheory.E.H2CurveOrder.TwLocGenPfSec
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPfSec

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  intro q _ V ζ ξ
  obtain ⟨s, hs, hf⟩ := hA q Γ(V, ⊤) ζ ξ
  let U : s → V.Opens := fun f => V.basicOpen f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, V.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := V.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f),
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩), ?_⟩
  rintro W g ⟨Y, h, _, ⟨i⟩, rfl⟩
  obtain ⟨a, n, hn⟩ := hf i.1 i.2
  refine ⟨a, ?_⟩
  have hle : (U i).ι ''ᵁ ⊤ ≤ V.basicOpen i.1 := by simp [U]
  have hu : IsUnit ((U i).ι.appTop.hom i.1) := by
    have := (V.toRingedSpace.isUnit_res_basicOpen i.1).map (V.presheaf.map (homOfLE hle).op).hom
    have e : V.presheaf.map (homOfLE (x := (U i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        V.presheaf.map (homOfLE (V.basicOpen_le i.1)).op ≫ V.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  have key : (U i).ι.appTop.hom ξ.1 = ((U i).ι.appTop.hom ζ.1) ^ (a : ZMod q).val := by
    have h0 : (U i).ι.appTop.hom (i.1 ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) = 0 := by rw [hn, map_zero]
    rw [map_mul, map_pow, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)
  have hc : ∀ x, (h ≫ (U i).ι).appTop.hom x = h.appTop.hom ((U i).ι.appTop.hom x) := fun x => by
    rfl
  show (h ≫ (U i).ι).appTop.hom ξ.1 = ((h ≫ (U i).ι).appTop.hom ζ.1) ^ _
  rw [hc, hc, key]
  exact map_pow _ _ _

theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.E.H2CurveOrder.TwLocGenPfSec.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.E.H2CurveOrder.TwLocGenPfSec
end

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPfSec

theorem root_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z : K)
    (hz : aeval z (cyclotomic q ℤ) = 0) : IsPrimitiveRoot z q := by
  have : NeZero (q : K) := ⟨hq⟩
  have h : (cyclotomic q K).IsRoot z := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    simpa [aeval_def] using hz
  exact (isRoot_cyclotomic_iff).1 h

theorem eq_pow_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (z x : K)
    (hz : IsPrimitiveRoot z q) (hx : IsPrimitiveRoot x q) : ∃ b : (ZMod q)ˣ, x = z ^ (b : ZMod q).val := by
  obtain ⟨i, hi, hzi⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hzi ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hzi]

theorem pow_ne_dom {K : Type} [CommRing K] (q : ℕ) [NeZero q] (z : K)
    (hz : IsPrimitiveRoot z q) (a b : (ZMod q)ˣ) (h : a ≠ b) :
    z ^ (a : ZMod q).val ≠ z ^ (b : ZMod q).val := by
  intro e
  apply h
  exact Units.ext (ZMod.val_injective q (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e))

theorem pow_q {A : Type} [CommRing A] (q : ℕ) (z : A) (hz : aeval z (cyclotomic q ℤ) = 0) : z ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval z) hp
  simp [hz] at this
  exact sub_eq_zero.1 this

theorem self_sq {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (x y : A)
    (hx : x ^ q = 1) (hy : y ^ q = 1) : ∃ w : A, x - y = (x - y) ^ 2 * w := by
  set d := x - y
  set u := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)
  have hdu : u * d = 0 := by
    have := geom_sum₂_mul x y q
    rw [hx, hy, sub_self] at this
    exact this
  have hyu : IsUnit y := isUnit_iff_exists_inv.2 ⟨y ^ (q - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne q)), hy]⟩
  set c : A := (q : A) * y ^ (q - 1)
  have hc : IsUnit c := hq.mul (hyu.pow _)
  have hmem : u - c ∈ Ideal.span {d} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy : Ideal.Quotient.mk (Ideal.span {d}) x = Ideal.Quotient.mk (Ideal.span {d}) y := by
      rw [Ideal.Quotient.eq]; exact Ideal.subset_span rfl
    simp only [u, c, map_sub, map_sum, map_mul, map_pow, map_natCast, hxy]
    rw [geom_sum₂_self, sub_self]
  obtain ⟨w0, hw0⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨cu, hcu⟩ := hc
  refine ⟨-(w0 * ↑cu⁻¹), ?_⟩
  have hdc : d * c = -(d ^ 2 * w0) := by
    have : c = u - w0 * d := by rw [hw0]; ring
    rw [this]; linear_combination hdu
  calc d = d * c * ↑cu⁻¹ := by rw [← hcu, mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [hdc]; ring

theorem self_pow {A : Type} [CommRing A] (d w : A) (h : d = d ^ 2 * w) (k : ℕ) : d = d ^ (k + 1) * w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc d = d ^ (k + 1) * w ^ k := ih
      _ = d ^ k * d * w ^ k := by ring
      _ = d ^ k * (d ^ 2 * w) * w ^ k := by rw [← h]
      _ = _ := by ring

theorem AlgPow_of : LateralTheory.E.H2CurveOrder.TwLocGenPfSec.AlgPow := by
  classical
  intro q _ A _ ζ ξ
  obtain ⟨hqA, hζ⟩ := ζ.2
  obtain ⟨-, hξ⟩ := ξ.2
  let f : (ZMod q)ˣ → A := fun a => ∏ b ∈ Finset.univ.erase a, (ξ.1 - ζ.1 ^ (b : ZMod q).val)

  have hdom : ∀ p : Ideal A, p.IsPrime → IsPrimitiveRoot (Ideal.Quotient.mk p ζ.1) q ∧
      IsPrimitiveRoot (Ideal.Quotient.mk p ξ.1) q := by
    intro p hp
    have hq : ((q : ℕ) : A ⧸ p) ≠ 0 := by
      have := hqA.map (Ideal.Quotient.mk p)
      rw [map_natCast] at this
      exact this.ne_zero
    have hm : ∀ z : A, aeval z (cyclotomic q ℤ) = 0 → aeval (Ideal.Quotient.mk p z) (cyclotomic q ℤ) = 0 := by
      intro z hz
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ p) z (cyclotomic q ℤ)
      rw [hz, map_zero] at this
      simpa using this
    exact ⟨root_dom q hq _ (hm _ hζ), root_dom q hq _ (hm _ hξ)⟩
  refine ⟨Set.range f, ?_, ?_⟩
  · by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h1, h2⟩ := hdom m hm.isPrime
    obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
    have hin : f b0 ∈ m := hsm (Ideal.subset_span ⟨b0, rfl⟩)
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hin
    simp only [f, map_prod, map_sub, map_pow, hb0] at hin
    rw [Finset.prod_eq_zero_iff] at hin
    obtain ⟨b, hb, e⟩ := hin
    exact pow_ne_dom q _ h1 b0 b (Finset.ne_of_mem_erase hb).symm (sub_eq_zero.1 e)
  · rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    have hnil : IsNilpotent (f a * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
      intro p hp
      have hp : p.IsPrime := hp
      obtain ⟨h1, h2⟩ := hdom p hp
      obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [f, map_mul, map_prod, map_sub, map_pow, hb0]
      by_cases hab : b0 = a
      · subst hab; simp
      · apply mul_eq_zero_of_left
        exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab, Finset.mem_univ _⟩) (sub_self _)
    obtain ⟨n, hn⟩ := hnil
    obtain ⟨w, hw⟩ := self_sq q hqA ξ.1 (ζ.1 ^ (a : ZMod q).val) (pow_q q _ hξ)
      (by rw [← pow_mul, mul_comm, pow_mul, pow_q q _ hζ, one_pow])
    refine ⟨n, ?_⟩
    rw [self_pow _ w hw n, pow_succ, mul_pow] at *
    calc f a ^ n * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n)
        = (f a ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n) * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n) := by ring
      _ = 0 := by rw [hn, zero_mul]

end LateralTheory.E.H2CurveOrder.TwLocGenPfSec
