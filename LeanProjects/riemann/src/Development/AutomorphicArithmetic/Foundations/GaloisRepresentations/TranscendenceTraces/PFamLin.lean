import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

noncomputable section

private def famAdd {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ τ' : Fam p I J) : Fam p I J where
  deg s := ⟨fun A => (τ.deg s).app A + (τ'.deg s).app A, fun t a => by
    simp only [AddMonoidHom.add_apply]
    rw [← (τ.deg s).nat t a, ← (τ'.deg s).nat t a]
    exact map_add _ _ _⟩
  comm A s t a := by
    simp only [AddMonoidHom.add_apply]
    rw [← τ.comm, ← τ'.comm]
    exact map_add _ _ _

private def famSmul {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (d : ℤ) (τ : Fam p I J) : Fam p I J where
  deg s := ⟨fun A => d • (τ.deg s).app A, fun t a => by
    simp only [AddMonoidHom.smul_apply]
    rw [← (τ.deg s).nat t a]
    exact map_zsmul _ _ _⟩
  comm A s t a := by
    simp only [AddMonoidHom.smul_apply]
    rw [← τ.comm]
    exact map_zsmul _ _ _

private theorem isIso_r {S : Scheme.{0}} (A : Sq (𝟙 S)) : IsIso A.r := A.pb.isIso_snd_of_isIso

private def resInv {S : Scheme.{0}} {R : Type} [CommRing R] (F : Shv R) (A : Sq (𝟙 S)) : Sec F A.V →+ Sec F A.U :=
  haveI := isIso_r A
  AddMonoidHom.mk' (fun a => Sec.res (inv A.r) a) (fun a b => map_add _ _ _)

private theorem resInv_apply {S : Scheme.{0}} {R : Type} [CommRing R] (F : Shv R) (A : Sq (𝟙 S)) [IsIso A.r] (a : Sec F A.V) :
    resInv F A a = Sec.res (inv A.r) a := rfl

private def famId (S : Scheme.{0}) {R : Type} [CommRing R] (I : Cx R) (d : ℤ) : Fam (𝟙 S) I I where
  deg s := ⟨fun A => d • resInv (I.X s) A, fun {A B} t a => by
    haveI := isIso_r A
    haveI := isIso_r B
    simp only [AddMonoidHom.smul_apply, resInv_apply]
    have e : t.g ≫ inv B.r = inv A.r ≫ t.k := by
      rw [IsIso.comp_inv_eq, Category.assoc, t.hr, IsIso.inv_hom_id_assoc]
    rw [show Sec.res t.g (d • Sec.res (inv B.r) a) = d • Sec.res t.g (Sec.res (inv B.r) a) from map_zsmul _ _ _,
      res_res, res_res, e]⟩
  comm A s t a := by
    haveI := isIso_r A
    simp only [AddMonoidHom.smul_apply, resInv_apply]
    rw [show Sec.map (I.d s t) (d • Sec.res (inv A.r) a) = d • Sec.map (I.d s t) (Sec.res (inv A.r) a) from map_zsmul _ _ _,
      map_res]

theorem UpperTheory.Gal.TranscendenceTraces.famLin_of :
    FibFin → FamLin := by
  intro hF q i
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' τ τ' hτ hτ'
    refine ⟨famAdd τ τ', fun A a => ?_, fun n A a => rfl⟩
    obtain ⟨b, hb, hs⟩ := hτ A a
    obtain ⟨b', hb', hs'⟩ := hτ' A a
    refine ⟨b + b', ?_, fun Ω _ _ x => ?_⟩
    · change (τ.deg 0).app A _ + (τ'.deg 0).app A _ = _
      rw [hb, hb']
      exact (map_add _ _ _).symm
    · haveI := Sq.finite A
      have hfin := hF A.r Ω x
      rw [show Sec.res x (b + b') = Sec.res x b + Sec.res x b' from map_add _ _ _, hs Ω x, hs' Ω x,
        ← finsum_mem_add_distrib hfin]
      refine finsum_mem_congr rfl fun z _ => ?_
      simp only [Wt.add, add_smul]
  · intro Z S p _ d w τ hτ
    refine ⟨famSmul d τ, fun A a => ?_, fun n A a => rfl⟩
    obtain ⟨b, hb, hs⟩ := hτ A a
    refine ⟨d • b, ?_, fun Ω _ _ x => ?_⟩
    · change d • (τ.deg 0).app A _ = _
      rw [hb]
      exact (map_zsmul _ _ _).symm
    · haveI := Sq.finite A
      have hfin := hF A.r Ω x
      rw [show Sec.res x (d • b) = d • Sec.res x b from map_zsmul _ _ _, hs Ω x]
      have := (zsmulAddGroupHom (α := Sec (tw q i) (gp Ω)) d).map_finsum_mem
        (fun z => w Ω (z ≫ A.v) • Sec.res z a) hfin
      refine this.trans ?_
      refine finsum_mem_congr rfl fun z _ => ?_
      simp only [Wt.smul, mul_smul, zsmulAddGroupHom_apply]
  · intro S d
    refine ⟨famId S _ d, fun A a => ?_, fun n a => ?_⟩
    · haveI := isIso_r A
      refine ⟨d • Sec.res (inv A.r) a, ?_, fun Ω _ _ x => ?_⟩
      · change d • resInv ((res _ (tw q i)).X 0) A (Sec.map (resι _ (tw q i)) a) = _
        rw [resInv_apply, ← map_res]
        exact (map_zsmul _ _ _).symm
      · have hf : fib A.r x = {x ≫ inv A.r} := by
          ext z
          simp only [fib, Set.mem_setOf_eq, Set.mem_singleton_iff]
          rw [IsIso.eq_comp_inv]
        rw [hf, finsum_mem_singleton]
        rw [show Sec.res x (d • Sec.res (inv A.r) a) = d • Sec.res x (Sec.res (inv A.r) a) from map_zsmul _ _ _, res_res]
        rfl
    · change d • resInv ((res _ (tw q i)).X n) (Sq.self (𝟙 S)) a = _
      haveI := isIso_r (Sq.self (𝟙 S))
      rw [resInv_apply]
      have e : inv (Sq.self (𝟙 S)).r = 𝟙 _ := IsIso.inv_id
      rw [e]
      exact congrArg (d • ·) (res_id a)

end
