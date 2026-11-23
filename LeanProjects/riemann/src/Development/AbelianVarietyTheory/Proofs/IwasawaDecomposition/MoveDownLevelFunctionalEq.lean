import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DnFv

open GlobalTheory.LvT.Pts GlobalTheory.Mem.Col2.LvProj
open Formalism.HermitianLatticesTheory (localization₂ dual)

theorem dual_map_smul {F V : Type} {iF : CommSemiring F} {iV : AddCommMonoid V} {iM : Module F V} (φ : Module.Dual F V) (a : F) (y : V) :
    φ (a • y) = a * φ y := by
  rw [map_smul, smul_eq_mul]

section TD

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem dn_extF_ok (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    ((A.deco c.1 (S.rep c)).dn P (TDat.extF (A.dnN c.1 (S.rep c) P) P.1 g)).Ok := by
  have hN := ht.dnN_eq c.1 (S.rep c) P
  refine (ht.ok c.1 (S.rep c)).dn P hM ?_ ?_ ?_ ?_
  · intro x hx y hy
    rw [← hN] at hx hy
    rw [extF_of_mem g hx, extF_of_mem g hy, extF_of_mem g ((localization₂ _ _).add_mem hx hy), redL_add hx hy, map_add]
  · intro r x hx
    rw [← hN] at hx
    rw [extF_of_mem g hx, extF_of_mem g ((localization₂ _ _).smul_mem r hx), redL_osmul r hx, map_smul]
    rfl
  · intro x hx
    rw [← hN] at hx
    exact extF_of_notMem g hx
  · obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
      by_contra H
      push Not at H
      exact hg (LinearMap.ext H)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨x.1, hN ▸ x.2, ?_⟩
    rw [extF_of_mem g (le_locP _ _ x.2), redL_coe]
    exact hz

theorem N_dnPt (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    A.N c.1 (A.dnPt P c g) = A.dnN c.1 (S.rep c) P := by
  have h := congrArg Deco.N (ht.dn_deco c.1 (S.rep c) P _ (dn_extF_ok ht P hM c hg))
  exact h.trans (ht.dnN_eq c.1 (S.rep c) P).symm

theorem f_dnPt (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    A.f c.1 (A.dnPt P c g) P = TDat.extF (A.dnN c.1 (S.rep c) P) P.1 g := by
  classical
  have h := congrArg (fun d => Deco.f d P) (ht.dn_deco c.1 (S.rep c) P _ (dn_extF_ok ht P hM c hg))
  refine h.trans ?_
  simp [Deco.dn]

theorem fv_dn (ho : A.Ok T) (ht : A.Tied T) (hl : A.Laws T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) {x : Fin n → E} {s : 𝓞 E} {G : Matrix (Fin n) (Fin n) E}
    (hG : G = (S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E))
    (hsx : s • x ∈ A.N (S.cl c.1 (A.dnPt P c g)).1 (S.rep (S.cl c.1 (A.dnPt P c g)))) :
    ∃ h : s • (G *ᵥ x) ∈ A.dnN c.1 (S.rep c) P,
      A.fv P (S.cl c.1 (A.dnPt P c g)) (Submodule.Quotient.mk ⟨_, hsx⟩) = g (Submodule.Quotient.mk ⟨_, h⟩) := by
  subst hG
  have hms : S.mv c.1 (A.dnPt P c g) • S.rep (S.cl c.1 (A.dnPt P c g)) = A.dnPt P c g := S.mv_smul c.1 _
  have e : (S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ (s • x) =
      s • ((S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ x) := by
    rw [← algebraMap_smul E s, ← algebraMap_smul E s, Matrix.mulVec_smul]
  have h1 := (ho.N_act c.1 (S.mv c.1 (A.dnPt P c g)) (S.rep (S.cl c.1 (A.dnPt P c g))) (s • x)).2 hsx
  rw [hms, N_dnPt ht P hM c hg, e] at h1
  refine ⟨h1, ?_⟩
  have h3 := ho.f_act c.1 (S.mv c.1 (A.dnPt P c g)) (S.rep (S.cl c.1 (A.dnPt P c g))) P (s • x)
  have h4 : redL (A.dnN c.1 (S.rep c) P) P.1 (s • ((S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ x)) =
      Submodule.Quotient.mk ⟨_, h1⟩ := redL_coe ⟨_, h1⟩
  rw [hms, f_dnPt ht P hM c hg, e, extF_of_mem g (le_locP _ _ h1), h4] at h3
  exact (fv_mk hl P _ ⟨_, hsx⟩).trans h3.symm

omit [NumberField K] [StarRing K] in

theorem exists_smul_mem_N {SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) {a : 𝓞 E} (ha : SepElt ST a) (P : ST)
    {y : Fin n → E} (hy : y ∈ d.Lsh) : ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧ s • y ∈ d.N := by
  have h := le_locP P.1 _ hy
  rw [localization_Lsh_eq_localization_N hd ha P rfl] at h
  exact (mem_locP _ _ _).1 h

end TD

end GlobalTheory.DnFv

end

open GlobalTheory.LvT.Pts GlobalTheory.Mem.Col2.LvProj in
open Formalism.HermitianLatticesTheory (localization₂ dual) in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.TC.dn_level_functional : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → ∀ (x : ↥(LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), (I.fm l u a).fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩) := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ x hx
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgr, -, hc⟩ := hc i hi
  have hLc := (hc u a).1
  clear hc
  have ha := sepElt_of_ok l.pr u
  have hmv := moveHyp_of_ok l.pr u v
  have hM : MoveHyp ((B.primes X).vT u) ∅ v := ⟨hmv.ne, hmv.st, fun w => absurd w.2 (Finset.notMem_empty _)⟩
  have hd : ∀ c', (((I.stp u a i).rep c').1.1.deco.1).Ok := fun c' => ((I.stp u a i).rep c').1.1.deco.2
  have hD : ∀ c', LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c')) = (((I.stp u a i).rep c').1.1.deco.1).Lsh := fun c' =>
    (@dualL_one B.fields.E B.fields.fieldE B.fields.nfE B.fields.starE _ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (fun _ => rfl) _ hgr _).trans (congrArg _ (hLc c'))
  have hx2 : (x.1 : Fin (B.R.N i) → B.fields.E) ∈ (((I.stp u a i).rep ((I.fm l u a).dn i v c.1 g)).1.1.deco.1).Lsh :=
    (SetLike.ext_iff.1 (hD _) _).1 x.2
  obtain ⟨s, hs, hsx⟩ := GlobalTheory.DnFv.exists_smul_mem_N (hd _) ha v hx2
  have hγ' : (γ.1.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) = _ := congrArg Units.val hγ
  obtain ⟨h1, h2⟩ := GlobalTheory.DnFv.fv_dn ((l.lev u a).lev i) ((l.lev u a).tied i) ((l.fmL u a).lev i) v hM c.1 hg hγ' hsx
  let s' : 𝓞 (I.rec7 l Z).host.E := s
  have hs' : (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) ≠ 0 := mk_ne_zero hs
  have f1 : ((I.fm l u a).fv i v _ (L.pr v _ (s' • x)) : Res v.1) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) * (I.fm l u a).fv i v _ (L.pr v _ x) :=
    (congrArg ((I.fm l u a).fv i v ((I.fm l u a).dn i v c.1 g)) (L.pr_smul v _ s' x)).trans
      (GlobalTheory.DnFv.dual_map_smul ((I.fm l u a).fv i v ((I.fm l u a).dn i v c.1 g)) _ _)
  let z : ↥(LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) := ⟨_, hx⟩
  have f2 : (g (L.prk v c.1 (s' • z)) : Res v.1) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) * g (L.prk v c.1 z) :=
    (congrArg g (L.prk_smul v c.1 s' z)).trans (GlobalTheory.DnFv.dual_map_smul g _ _)
  refine mul_left_cancel₀ hs' (f1.symm.trans (Eq.trans ?_ f2))
  have e1 := hL.1 v _ (s' • x) hsx
  have e2 := hL.2 v c.1 (s' • z) h1
  exact (congrArg _ e1).trans (h2.trans (congrArg g e2.symm))
