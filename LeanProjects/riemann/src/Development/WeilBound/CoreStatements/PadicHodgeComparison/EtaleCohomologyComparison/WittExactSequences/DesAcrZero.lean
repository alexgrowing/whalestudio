import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesUnOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ResKill
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SemilinearOfAdditive
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.UDAuxFil

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem acr_zero_eq (A : PAlg l) (x : A.Acr 0) : x = 0 := by
  have h1 : (1 : A.Acr 0) = 0 := by simpa using A.pow_l_acr 0
  rw [← mul_one x, h1, mul_zero]

theorem des_Acr_zero (s : Acris l) : Des (AcrF l 0) s :=
  des_span (testι l) (AcrF l 0) {s} (fun _ _ => Or.inr fun A x => by
    have hx : x = 0 := acr_zero_eq l A x
    rw [hx, smul_zero]) s (Ideal.subset_span rfl)

theorem des_Acr_one (h : ObFacts l) (h1 : RAcr1 l) (k : ℕ) :
    Des (AcrF l 1) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  obtain ⟨N, _, _, M, τ, hN, hτ, hn⟩ := h1
  have h0 := des_tens l h N M hN k
  let σ : Ainf l →+* Ob l := WittVector.constantCoeff
  have e1 : Des (toPf l ⋙ tensF l (Ob l) N ⋙ ModuleCat.restrictScalars σ) (rtW l k) := by
    refine (des_semi σ (testι l) (toPf l ⋙ tensF l (Ob l) N ⋙ ModuleCat.restrictScalars σ) (toPf l ⋙ tensF l (Ob l) N)
      (fun A => AddMonoidHom.id _) (fun A a x => rfl) (fun A => Function.bijective_id) (fun f x => rfl) (rtW l k)).2 ?_
    have hc : σ (rtW l k) = rt l k := (rtW_dvd l k).2
    rw [hc]; exact h0
  refine (des_semi (algebraMap (Ainf l) (Acris l)) (testι l) (toPf l ⋙ tensF l (Ob l) N ⋙ ModuleCat.restrictScalars σ)
    (AcrF l 1) (fun A => (τ A).toAddMonoidHom) (fun A a x => ?_) (fun A => (τ A).bijective) (fun f x => hn _ _ f x) (rtW l k)).1 e1
  refine (hτ A a x).trans ?_
  change _ = A.cris 1 (algebraMap (Ainf l) (Acris l) a) * τ A x
  rw [A.cris_algebraMap]; rfl

theorem mkAcr_surj (A : PAlg l) (m : ℕ) : Function.Surjective (A.mkAcr m) := Ideal.Quotient.mk_surjective

theorem acr_smul_eq (A : PAlg l) (m : ℕ) (a : Ainf l) (z : A.Acr m) :
    (algebraMap (Ainf l) (Acris l) a) • z = A.mkAcr m (algebraMap A.W A.Acr0 (A.sW a)) * z := by
  rw [Algebra.smul_def]; exact congrArg (· * z) (A.cris_algebraMap m a)

theorem des_span_dvd {R : Type} [CommRing R] (F : PAlg l ⥤ ModuleCat.{0} R) (a b : R) (hab : a ∣ b) (ha : Des F a) : Des F b :=
  des_span (testι l) F {a} (fun c hc => Or.inl (by rw [Set.mem_singleton_iff.1 hc]; exact ha)) b
    (Ideal.mem_span_singleton.2 hab)

theorem seq_smul (n : ℕ) (A : PAlg l) (α : A.Acr 1 →+ A.Acr (n + 1))
    (hmk : ∀ y : A.Acr0, α (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y)) (a : Ainf l) (x : A.Acr 1) :
    α (algebraMap (Ainf l) (Acris l) a • x) = algebraMap (Ainf l) (Acris l) a • α x := by
  obtain ⟨y, rfl⟩ := mkAcr_surj l A 1 x
  rw [acr_smul_eq, acr_smul_eq, ← map_mul, hmk, hmk, ← map_mul, mul_left_comm]

theorem seq_nat (n : ℕ) {A B : PAlg l} (f : A ⟶ B) (α : A.Acr 1 →+ A.Acr (n + 1)) (α' : B.Acr 1 →+ B.Acr (n + 1))
    (hmk : ∀ y : A.Acr0, α (A.mkAcr 1 y) = A.mkAcr (n + 1) ((l : A.Acr0) ^ n * y))
    (hmk' : ∀ y : B.Acr0, α' (B.mkAcr 1 y) = B.mkAcr (n + 1) ((l : B.Acr0) ^ n * y)) (x : A.Acr 1) :
    α' (PAlg.mapAcr f 1 x) = PAlg.mapAcr f (n + 1) (α x) := by
  obtain ⟨y, rfl⟩ := mkAcr_surj l A 1 x
  change α' ((PAlg.pdOk_hom f).acr 1 (A.mkAcr 1 y)) = (PAlg.pdOk_hom f).acr (n + 1) (α (A.mkAcr 1 y))
  rw [hmk, PAlg.PdOk.acr_mk, PAlg.PdOk.acr_mk, hmk']
  simp only [map_mul, map_pow, map_natCast]

theorem red_surj (A : PAlg l) (n : ℕ) : Function.Surjective (A.red (Nat.le_succ n)) := fun x => by
  obtain ⟨y, rfl⟩ := mkAcr_surj l A n x
  exact ⟨A.mkAcr (n + 1) y, rfl⟩

theorem des_Acr_succ (h2 : RAcrSeq l) (n : ℕ)
    (h1k : ∀ k, Des (AcrF l 1) (algebraMap (Ainf l) (Acris l) (rtW l k)))
    (hnk : ∀ k, Des (AcrF l n) (algebraMap (Ainf l) (Acris l) (rtW l k))) (k : ℕ) :
    Des (AcrF l (n + 1)) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  obtain ⟨α, hαmk, hαe⟩ := h2 n
  let σ := algebraMap (Ainf l) (Acris l)
  have := (des_ses σ σ σ (testι l) (AcrF l 1) (AcrF l (n + 1)) (AcrF l n) (fun A => α A)
    (fun A => ((redF l (Nat.le_succ n)).app A).hom.toAddMonoidHom)
    (fun A a x => seq_smul l n A (α A) (hαmk A) a x)
    (fun A a x => ((redF l (Nat.le_succ n)).app A).hom.map_smul (σ a) x)
    (fun {A B} f x => seq_nat l n f (α A) (α B) (hαmk A) (hαmk B) x)
    (fun {A B} f x => congrArg (fun g => ModuleCat.Hom.hom g x) ((redF l (Nat.le_succ n)).naturality f))
    (fun A => (hαe A).1) (fun A => (hαe A).2)
    (fun A => red_surj l A n) (rtW l (k + 2))).1 (h1k _) (hnk _)
  exact des_span_dvd l _ _ _ (map_dvd σ (rtW_dvd l k).1) this

theorem un_kill (A : PAlg l) (n : ℕ) (x : (UnF l n).obj A) : ((l : Ainf l) ^ n) • x = 0 := by
  have h0 : (l : A.Un n) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ n})), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  refine (Algebra.smul_def (A := A.Un n) _ x).trans ?_
  rw [map_pow, map_natCast, h0, zero_mul]

theorem acr_kill (A : PAlg l) (n : ℕ) (x : A.Acr n) : algebraMap (Ainf l) (Acris l) ((l : Ainf l) ^ n) • x = 0 := by
  rw [acr_smul_eq]
  simp only [map_pow, map_natCast]
  rw [A.pow_l_acr, zero_mul]

theorem fil_kill (A : PAlg l) (n r : ℕ) (x : (FilF l n r).obj A) :
    algebraMap (Ainf l) (Acris l) ((l : Ainf l) ^ n) • x = 0 :=
  Subtype.ext (acr_kill l A n x.1)

theorem des_of_map {R : Type} [CommRing R] (F : PAlg l ⥤ ModuleCat.{0} R) (σ : Ainf l →+* R) (n : ℕ)
    (hk : ∀ (A : PAlg l) (x : F.obj A), σ ((l : Ainf l) ^ n) • x = 0) (hr : ∀ k, Des F (σ (rtW l k)))
    (s : Ainf l) (hs : s ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l)))) : Des F (σ s) := by
  have hm := Ideal.mem_map_of_mem σ hs
  rw [Ideal.map_span] at hm
  refine des_span (testι l) F _ ?_ _ hm
  rintro _ ⟨b, hb, rfl⟩
  rcases hb with rfl | ⟨k, rfl⟩
  · exact Or.inr hk
  · exact Or.inl (hr k)

theorem des_Acr (h : ObFacts l) (h1 : RAcr1 l) (h2 : RAcrSeq l) (n k : ℕ) :
    Des (AcrF l n) (algebraMap (Ainf l) (Acris l) (rtW l k)) := by
  induction n generalizing k with
  | zero => exact des_Acr_zero l _
  | succ n ih => exact des_Acr_succ l h2 n (des_Acr_one l h h1) ih k

theorem des_Fil (h : RIn l) (n r k : ℕ) : Des (FilF l n r) (algebraMap (Ainf l) (Acris l) (rtW l k)) :=
  des_Fil_of l h (fun n k => des_Acr l h.1 h.2.1 h.2.2.1 n k) n r k

theorem out_of_rin (h : RIn l) : Out l := fun s hs n => by
  have hw := wm_span l h.1 s hs n
  refine ⟨?_, ?_, fun r => ?_⟩
  · exact des_of_map l (UnF l n) (RingHom.id _) n (fun A x => un_kill l A n x) (des_Un l h.1 h.2.2.2.1 n) s hw
  · exact des_of_map l (AcrF l n) (algebraMap _ _) n (fun A x => acr_kill l A n x) (des_Acr l h.1 h.2.1 h.2.2.1 n) s hw
  · exact des_of_map l (FilF l n r) (algebraMap _ _) n (fun A x => fil_kill l A n r x) (des_Fil l h n r) s hw

end CrystallineSemistableComparison.D
