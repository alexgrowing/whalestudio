import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

namespace UpperTheory.Gal.Mod.FrobeniusTorsors

open UpperTheory.Gal.TranscendenceTraces GlobalTheory.SS.FrobField

private theorem prim_pow {m : ℕ} {A : Type} [CommRing A] (ζ : Prim m A) : ζ.1 ^ m = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

private theorem prim_ex (m : ℕ) [NeZero m] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hm : IsUnit (m : Ω)) :
    Nonempty (Prim m Γ(gp Ω, ⊤)) := by
  haveI : NeZero (m : Ω) := ⟨hm.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  refine ⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ⟨ζ, hm, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ.isRoot_cyclotomic (NeZero.pos m)

private theorem tw_sub (m : ℕ) [NeZero m] (hm : m = 1) (i : ℤ) {U : Scheme.{0}} (a b : Sec (tw m i) U) : a = b := by
  subst hm
  have e : (1 : ULift.{1} (ZMod 1)) = 0 := Subsingleton.elim _ _
  rw [← one_smul (ULift.{1} (ZMod 1)) a, ← one_smul (ULift.{1} (ZMod 1)) b, e, zero_smul, zero_smul]

private theorem frob_top (Ω : Type) [Field Ω] (p f : ℕ) (hp : p.Prime) (h : (p : Γ(gp Ω, ⊤)) = 0) (c : Γ(gp Ω, ⊤)) :
    (absFrob (gp Ω) p f hp h).appTop.hom c = c ^ p ^ f := rfl

private theorem frob_pt (m : ℕ) [NeZero m] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p f : ℕ) (hp : p.Prime)
    (h : (p : Γ(gp Ω, ⊤)) = 0) (hm : IsUnit (m : Ω)) (y : Sec (tw m 0) (gp Ω)) :
    Sec.res (absFrob (gp Ω) p f hp h) y = y := by
  obtain ⟨ζ⟩ := prim_ex m Ω hm
  obtain ⟨φ, -, hφ⟩ := secFun_holds m 0 (gp Ω) ζ y
  have hI := GlobalTheory.T.tateTwist_sections_locally_generated m 0
  have key : Sec.res (absFrob (gp Ω) p f hp h) (twGen 0 ζ) = twGen 0 ζ := by
    rw [hI.2.2.2.1]
    by_cases h1 : m = 1
    · exact tw_sub m h1 0 _ _
    · have hpΩ : (p : Ω) = 0 := by
        have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom h
        rw [map_natCast, map_zero] at this
        exact this
      have hcop : Nat.Coprime (p ^ f) m := by
        refine Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_)
        rintro ⟨k, hk⟩
        apply hm.ne_zero
        rw [hk, Nat.cast_mul, hpΩ, zero_mul]
      haveI : Fact (1 < m) := ⟨by
        have := NeZero.ne m
        omega⟩
      rw [hI.2.2.2.2.1 (gp Ω) ζ _ (ZMod.unitOfCoprime (p ^ f) hcop)]
      · rw [zpow_zero, Units.val_one, ZMod.val_one, one_smul]
      · show (absFrob (gp Ω) p f hp h).appTop.hom ζ.1 = ζ.1 ^ ((ZMod.unitOfCoprime (p ^ f) hcop : ZMod m)).val
        rw [frob_top, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
        conv_lhs => rw [← Nat.mod_add_div (p ^ f) m]
        rw [pow_add, pow_mul, prim_pow ζ, one_pow, mul_one]
  apply ptInj_holds m 0
  intro Ω' _ _ x
  rw [res_res, hφ Ω' _, hφ Ω' x, ← res_res, key, Subsingleton.elim (pt (x ≫ absFrob (gp Ω) p f hp h)) (pt x)]

private theorem frob_sec (m : ℕ) [NeZero m] (U : Scheme.{0}) (p f : ℕ) (hp : p.Prime) (h : (p : Γ(U, ⊤)) = 0)
    (hm : IsUnit (m : Γ(U, ⊤))) (a : Sec (tw m 0) U) : Sec.res (absFrob U p f hp h) a = a := by
  refine ptInj_holds m 0 U _ _ fun Ω _ _ x => ?_
  have hΩ : (p : Γ(gp Ω, ⊤)) = 0 := cast_zero_of_hom x h
  have hmΩ : IsUnit (m : Ω) := by
    have h1 := (hm.map x.appTop.hom).map (Scheme.ΓSpecIso (.of Ω)).hom.hom
    simpa using h1
  rw [res_res, ← absFrob_nat x p f hp hΩ h, ← res_res]
  exact frob_pt m Ω p f hp hΩ hmΩ _

variable {X : Scheme.{0}}

private noncomputable def sc (A : Sq (𝟙 X)) : A.U ⟶ A.V :=
  A.pb.lift A.u (𝟙 _) (by simp)

private theorem sc_v (A : Sq (𝟙 X)) : sc A ≫ A.v = A.u := A.pb.lift_fst _ _ _

private theorem sc_r (A : Sq (𝟙 X)) : sc A ≫ A.r = 𝟙 _ := A.pb.lift_snd _ _ _

private theorem r_sc (A : Sq (𝟙 X)) : A.r ≫ sc A = 𝟙 _ := by
  refine A.pb.hom_ext ?_ ?_
  · rw [Category.assoc, sc_v, Category.id_comp, ← A.pb.w, Category.comp_id]
  · rw [Category.assoc, sc_r, Category.comp_id, Category.id_comp]

private theorem sc_nat {A B : Sq (𝟙 X)} (t : A.To B) : sc A ≫ t.k = t.g ≫ sc B := by
  refine B.pb.hom_ext ?_ ?_
  · rw [Category.assoc, t.hv, sc_v, Category.assoc, sc_v, t.hu]
  · rw [Category.assoc, t.hr, ← Category.assoc, sc_r, Category.id_comp, Category.assoc, sc_r, Category.comp_id]

private noncomputable def fk (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (A : Sq (𝟙 X)) : A.U ⟶ A.V :=
  absFrob A.U p f hp (cast_zero_of_hom A.u h) ≫ sc A

private theorem fk_nat (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {A B : Sq (𝟙 X)} (t : A.To B) :
    t.g ≫ fk p f hp h B = fk p f hp h A ≫ t.k := by
  unfold fk
  rw [← Category.assoc, ← absFrob_nat t.g p f hp (cast_zero_of_hom A.u h) (cast_zero_of_hom B.u h), Category.assoc,
    ← sc_nat, Category.assoc]

private noncomputable def fam0 (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (F : GlobalTheory.EtC.Shv R) :
    Fam0 (𝟙 X) F F where
  app A := (F.obj.map (fk p f hp h A).op).hom.toAddMonoidHom
  nat {A B} t a := (res_res t.g (fk p f hp h B) a).trans
    ((congrArg (fun e => Sec.res e a) (fk_nat p f hp h t)).trans (res_res (fk p f hp h A) t.k a).symm)

private noncomputable def fam (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (I : Cx R) :
    Fam (𝟙 X) I I where
  deg s := fam0 p f hp h (I.X s)
  comm A s t a := (map_res (I.d s t) (fk p f hp h A) a)

private theorem fk_self (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) :
    fk p f hp h (Sq.self (𝟙 X)) = absFrob X p f hp h := by
  unfold fk
  have h1 : sc (Sq.self (𝟙 X)) = 𝟙 _ := (Category.comp_id (sc (Sq.self (𝟙 X)))).symm.trans (sc_r (Sq.self (𝟙 X)))
  rw [h1]
  exact Category.comp_id _

private theorem fam_app (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (I : Cx R) (s : ℤ)
    (A : Sq (𝟙 X)) (a : Sec (I.X s) A.V) : ((fam p f hp h I).deg s).app A a = Sec.res (fk p f hp h A) a := rfl

private theorem fam_sums (m : ℕ) [NeZero m] (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (hm : IsUnit (m : Γ(X, ⊤))) :
    (fam p f hp h (res _ (tw m 0))).Sums (Wt.const X 1) := by
  intro A a
  have hmU : IsUnit (m : Γ(A.U, ⊤)) := by simpa using hm.map A.u.appTop.hom
  refine ⟨Sec.res (sc A) a, ?_, fun Ω _ _ x => ?_⟩
  · rw [fam_app, ← map_res]
    refine congrArg (Sec.map (resι _ _)) ?_
    unfold fk
    rw [← res_res]
    exact frob_sec m A.U p f hp _ hmU _
  · have hf : fib A.r x = {x ≫ sc A} := by
      ext z
      constructor
      · intro hz
        have hz' : z ≫ A.r = x := hz
        rw [Set.mem_singleton_iff, ← hz', Category.assoc, r_sc, Category.comp_id]
      · rintro rfl
        change (x ≫ sc A) ≫ A.r = x
        rw [Category.assoc, sc_r, Category.comp_id]
    rw [hf, finsum_mem_singleton, res_res]
    exact (one_smul ℤ _).symm

end UpperTheory.Gal.Mod.FrobeniusTorsors

open UpperTheory.Gal.Mod.FrobeniusTorsors in
theorem UpperTheory.Gal.Mod.frobTors :
    FrobTors := by
  intro m _ X p f hp h hm k x
  have e1 := (TranscendenceTraces.trChar_holds m 0 (𝟙 X) (Wt.const X 1) (TranscendenceTraces.wtLin_holds.2.2 (𝟙 X) 1) hm).2.2 _
    (fam_sums m p f hp h hm) k
  have e2 := (TranscendenceTraces.trLin_holds m k 0).2.2 X 1 hm x
  rw [e1, one_smul] at e2
  obtain ⟨a, ha⟩ := (TranscendenceTraces.rpBasic_holds _ (res _ (tw m 0)) X k).1 x
  have h1 := (TranscendenceTraces.rpBasic_holds _ (res _ (tw m 0)) X k).2.2.2.1 X (absFrob X p f hp h) x a ha
  have h2 := TranscendenceTraces.rpOp_holds _ _ (fam p f hp h (res _ (tw m 0))) k x a ha
  rw [e2] at h2
  refine ((TranscendenceTraces.rpBasic_holds _ _ X k).2.2.1 _ _ _ _ h1 h2).2.1 ?_
  exact (congrArg (fun e => Sec.res e a) (fk_self p f hp h)).symm
