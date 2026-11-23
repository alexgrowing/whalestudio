import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.AlgResPropsPf
open LateralTheory.E.t_E3Cut

theorem cancel {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : AlgRes (f ≫ g)) : AlgRes g := by
  intro Q hQ c
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := h Q hQ c
  refine ⟨p.map f.hom, ⟨n, ?_⟩, ?_⟩
  · rw [Polynomial.coeff_map]; simpa using hn
  · rw [Polynomial.eval₂_map]; simpa using hp

theorem integral {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.IsIntegral) : AlgRes f := by
  intro Q hQ c
  obtain ⟨p, hm, hp⟩ := h c
  refine ⟨p, ⟨p.natDegree, ?_⟩, ?_⟩
  · rw [← Polynomial.leadingCoeff, hm.leadingCoeff, map_one]
    exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
  · rw [hp]; exact Q.zero_mem

theorem loc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] :
    AlgRes (CommRingCat.ofHom (algebraMap A B)) := by
  intro Q hQ c
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
  refine ⟨Polynomial.C (s : A) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩
  · have hu : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
    intro hm
    apply hQ.ne_top
    apply Q.eq_top_of_isUnit_mem hm
    simpa [Polynomial.coeff_C, Polynomial.coeff_X] using hu
  · have := IsLocalization.mk'_spec B a s
    simp only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [mul_comm, this, sub_self]; exact Q.zero_mem

def Comp : Prop :=
  ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)

def Push : Prop :=
  ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v

def EtAlg : Prop := ∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f

theorem AlgResProps_of (h1 : Comp) (h2 : Push) (h3 : EtAlg) : LateralTheory.E.t_E3Cut.AlgResProps :=
  ⟨fun f g hf hg => h1 f g hf hg, fun f g h => cancel f g h, fun f g u v h hf => h2 f g u v h hf,
    fun f h => h3 f h, fun f h => integral f h, fun A B _ _ _ S _ => loc A B S⟩

end LateralTheory.E.AlgResPropsPf
